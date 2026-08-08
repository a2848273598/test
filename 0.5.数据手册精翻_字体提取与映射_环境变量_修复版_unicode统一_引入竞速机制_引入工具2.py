# -*- coding: utf-8 -*-
r"""
阶段 0：从整本 PDF 提取实际可见字体，选择尽量少的代表单页 PDF，上传 GitHub，
调用大模型生成全书统一的中文字体映射，下载并验证字体资源。

默认读取同目录下：
    1.数据手册精翻_转录_环境变量_并发批量.py
中的 PDF_INPUT、GitHub 仓库等配置。

最终主要输出：
    精翻工程\_图像处理公共资源\font_mapping.json
    精翻工程\_图像处理公共资源\resources\fonts\...

安装：
    python -m pip install -U pymupdf requests fonttools

运行：
    python "0.2.数据手册精翻_字体提取与映射_环境变量_修复版_unicode统一_引入竞速机制.py"

常用参数：
    --force          强制重新分析、重新请求模型并覆盖映射
    --skip-upload    已确认代表单页 PDF 在 GitHub 上时跳过上传
    --pdf "...pdf"  显式指定 PDF
    --race-copies N  每轮字体映射竞速副本数，默认 5
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import math
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from collections import Counter, defaultdict
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from dataclasses import dataclass, field
from html.parser import HTMLParser
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import quote, urlparse

try:
    import pymupdf as fitz  # PyMuPDF 新名称
except ImportError:  # 兼容旧导入名
    import fitz  # type: ignore

import requests


# ============================================================
# 1. 配置区域
# ============================================================

BASE_URL = os.environ.get("EASYGPT_URL", "").strip()
MODEL = os.environ.get("EASYGPT_MODEL", "").strip()

API_KEYS = [
    os.environ.get(f"EASYGPT_KEY{i}", "").strip()
    for i in range(1, 9)
]
API_KEYS = [key for key in API_KEYS if key]

KEY_MAX_FAILS = 3
PROXY_URL = "http://127.0.0.1:7890"

TRANSCRIBE_SCRIPT_NAME = "1.数据手册精翻_转录_环境变量_并发批量.py"
OUTPUT_ROOT_NAME = "精翻工程"
SHARED_RESOURCE_DIR_NAME = "_图像处理公共资源"
FONT_DIR_RELATIVE = Path("resources") / "fonts"
FONT_MAPPING_FILE_NAME = "font_mapping.json"
FONT_MAPPING_META_FILE_NAME = "font_mapping_meta.json"
FONT_STAGE_WORK_DIR_NAME = "_字体提取与映射"
PDF_PAGES_DIR_NAME = "单页PDF"
REJECTED_FONT_CANDIDATES_FILE_NAME = "02_rejected_font_candidates.json"
MODEL_FONT_VALIDATION_REPORTS_FILE_NAME = "01_model_font_validation_reports.json"

RETRY_COUNT = 10_000
RETRY_DELAY = 5
REQUEST_INTERVAL = 0

# 同一轮字体映射采用独立副本竞速。每个副本仅在自己的工作目录和字体目录中
# 写入；只有最先通过模型协议、字体下载和本地完整验证的副本，才会把字体
# 原子晋升到公共 resources/fonts 目录。可通过 --race-copies 覆盖。
MAPPING_RACE_COPY_COUNT = 10
MAPPING_RACE_COPY_DIR_NAME = "竞速副本"

# HTTP 连接超时和底层流读取超时。
REQUEST_CONNECT_TIMEOUT_SECONDS = 60.0
STREAM_SOCKET_READ_TIMEOUT_SECONDS = 1800.0
RESPONSE_HEADER_ABSOLUTE_TIMEOUT_SECONDS = 1800.0
REQUEST_TIMEOUT = (
    REQUEST_CONNECT_TIMEOUT_SECONDS,
    STREAM_SOCKET_READ_TIMEOUT_SECONDS,
)

# 流式请求可见性和超时。
STREAM_QUEUE_POLL_INTERVAL_SECONDS = 1.0
STREAM_PROGRESS_PRINT_INTERVAL_SECONDS = 10.0
STREAM_FIRST_DATA_TIMEOUT_SECONDS = 600.0
STREAM_IDLE_TIMEOUT_SECONDS = 300.0
STREAM_ABSOLUTE_TIMEOUT_SECONDS = 1800.0

# 异步报告页兜底和断点续传。
ASYNC_REPORT_POLL_INTERVAL_SECONDS = 2.0
ASYNC_REPORT_PROGRESS_PRINT_INTERVAL_SECONDS = 10.0
ASYNC_REPORT_REQUEST_TIMEOUT_SECONDS = 20.0
ASYNC_REPORT_PROCESSING_TIMEOUT_SECONDS = 1800.0
ASYNC_REPORT_RESUME_ENABLED = True

# 每种字体在提示词中最多列出的样本文字数量。
MAX_SAMPLES_PER_FONT = 5
# 每条样本文字截断长度。
MAX_SAMPLE_TEXT_LENGTH = 120
# 提示词中每种字体最多列出多少个出现页码。
MAX_LISTED_PAGES_PER_FONT = 40
# 下载后用于验证中文覆盖的测试字符。
FONT_GLYPH_TEST_TEXT = "中文电源电压监控保护绝对最大额定值技术数据手册"
# 字体文件最低大小。极小文件大概率是 HTML 错误页或下载失败。
MIN_FONT_FILE_SIZE = 10_000

# 与阶段 4 实际写入方式一致的本地精确往返测试文本。
FONT_ROUNDTRIP_FIXED_TEST_STRINGS = (
    "中文电源电压监控保护绝对最大额定值技术数据手册",
    "器不量年行更路料串理便利",
    "控制器寄存器转换器驱动器",
    "测量数量容量电量",
    "不能不同不使用不连接",
    "年月更新执行管理系列",
    "BQ769x0",
    "ADC",
    "I²C",
    "3.3 V",
    "GPIO1",
    "R12",
    "VIN",
    "VOUT",
    "表1（测试）",
    "±25 ℃",
    "10 kΩ",
)
FONT_ROUNDTRIP_CHUNK_SIZE = 24
FONT_VALIDATION_VERSION = 1

DEBUG_PRINT_STREAM = True
DEBUG_PRINT_RAW_SSE = False
DEBUG_PRINT_REASONING_CONTENT = False

# 如果已有当前版本映射且未使用 --force，则直接结束。
SKIP_WHEN_MAPPING_EXISTS = True


# ============================================================
# 2. 阶段 0 提示词
# ============================================================

FONT_MAPPING_PROMPT_TEMPLATE = r"""
## 任务：为 PDF 中实际使用的字体建立全书统一的中文字体映射

现在需要把一整本 PDF 中的英文内容翻译为中文。

程序已经从整本 PDF 的实际可见文字中提取字体信息。本轮将提供一组需要判断的字体，以及这些字体当前已有的相关证据页面。

本轮字体清单可能包含整本 PDF 的全部字体，也可能只包含经过上一轮判断后仍需补充证据的字体。无论属于哪种情况，都只需处理本轮字体清单中列出的映射键。

请查看字体清单、文字样例和全部相关页面，为本轮列出的每一个原始字体返回一个字体映射对象或 null。

映射后的中文应尽量保持原文的视觉层级和排版风格，例如正文、标题、表头、注释、粗体、斜体、窄体、等宽字体等应尽可能与原文协调。

请注意：专业术语、产品型号、寄存器名、引脚名、节点名、变量名、数字以及部分英文可能在最终译文中保留原文。因此，原英文字体与映射后的中文字体可能同时出现在同一行，所选中文字体也应当与原有英文字体在视觉上协调。

### 本轮待处理字体清单

以下内容来自程序对整本 PDF 实际可见文字的提取。

每个条目中的“映射键”是最终 JSON 必须使用的键，不得修改、合并、遗漏或增加。

{字体清单}

### 当前已经提供的相关单页 PDF

以下页面是本轮待处理字体当前已有的全部证据页面，其中可能包括初始代表页面和后续补充页面。

请综合查看当前列出的全部相关页面。每个页面条目会列出该页包含的本轮待处理字体；字体清单中还提供了实际承载的原文样例、页码、字号和位置，可用于区分同一页面中的不同字体。

{代表页面清单}

### 禁止重复使用的失败字体

{禁止重复使用的失败字体}

以上失败记录来自当前生产环境中的真实下载、字体结构扫描或 PyMuPDF 写入—子集化—保存—重新提取测试。

不得再次返回与失败记录具有相同 `target_font_file`、相同 `download_url` 或相同 SHA256 的字体资源。

不得仅改文件名后继续返回相同字体文件，也不得返回同一字体文件的镜像 URL。

### 最重要的分类原则

本任务中的 null 与非 null，必须根据“该字体实际承载的字符是否属于人类书写语言”来区分。

正确的分类方法如下。

#### 一、必须返回字体映射对象的情况

只要某个字体在当前提供的任意相关页面中，实际承载过至少一个属于人类书写语言的文字字符，就必须返回字体映射对象，不得返回 null。

这里所说的语言文字包括但不限于：

- 中文及其他汉字；
- 英文字母；
- 其他语言的字母、音节文字或表意文字；
- 英文单词、句子、标题、正文、表头、说明和注释；
- 缩写和专业术语；
- 产品型号；
- 寄存器名；
- 引脚名；
- 节点名；
- 信号名；
- 变量名；
- 单位名称或由字母表示的单位；
- 由字母构成或包含字母的代码和标识；
- 依赖具体书写语言才能成立的其他文字内容。

即使某段内容在最终译文中会完整保留原文、不进行翻译，只要其中包含语言文字，该字体仍然必须返回字体映射对象。

例如，以下内容都属于语言文字，必须返回字体映射对象：

- `Power Supply`
- `ABSOLUTE MAXIMUM RATINGS`
- `VCC`
- `GND`
- `RESET`
- `GPIO1`
- `TPS5430`
- `R12`
- `VIN`
- `VOUT`
- `Table 1`
- `Figure 2`
- `3.3 V`
- `25 MHz`

型号、寄存器名、引脚名、节点名、变量名和单位即使通常不翻译，只要包含字母或其他语言文字，也属于非 null。

#### 二、允许返回 null 的情况

只有当某个字体在当前已经提供的全部相关页面中，实际承载的所有内容都不属于任何具体书写语言，而只是跨语言通用的符号或数字时，才允许返回 null。

允许判定为 null 的内容包括：

- 纯数学运算符，例如 `+`、`-`、`*`、`/`、`×`、`÷`；
- 纯数学关系符号，例如 `=`、`≠`、`<`、`>`、`≤`、`≥`、`≈`；
- 纯数学符号，例如 `±`、`√`、`∞`、`∑`、`∫`；
- 纯箭头，例如 `←`、`→`、`↑`、`↓`；
- 纯几何图形，例如 `○`、`●`、`□`、`■`、`△`；
- 图标；
- Dingbats；
- 纯装饰性或示意性特殊字形；
- 纯阿拉伯数字，例如 `0`、`123`、`3.3`、`2025`；
- 在公式、尺寸、序号或技术图示中作为通用记号使用的纯数字和纯符号。

纯阿拉伯数字可以视为跨语言通用的数字符号，因此，如果一个字体在所有当前证据页中只承载纯数字，可以返回 null。

但是，只要数字与字母或其他语言文字共同构成内容，例如 `VCC1`、`GPIO2`、`R12`、`TPS5430`、`Table 1`、`3.3 V`，就属于语言文字，必须返回字体映射对象。

#### 三、混合内容的处理

如果同一个字体同时承载语言文字和通用符号，必须返回字体映射对象。

例如，一个字体承载了：

- 英文字母和数学运算符；
- 型号和数字；
- 正文和标点；
- 引脚名和箭头；
- 单位字母和数值；
- 标题和图形符号；

都必须返回字体映射对象。

只要发现一个语言文字字符，就足以确定该字体为非 null。不能因为该字体的大部分内容是数字或符号而返回 null。

可以把最终判定规则概括为：

- 出现过任何语言文字字符：返回字体映射对象；
- 全部内容都是非语言的通用数字、数学符号、图形符号或图标：返回 null。

#### 四、标点符号的处理

需要结合标点符号的实际用途判断：

- 如果符号是公式、运算、技术图示或图形界面中的独立通用符号，可以按非语言符号处理；
- 如果标点用于自然语言标题、正文、说明、注释或其他语言文本的书写结构，则它属于语言书写内容的一部分。

通常，同一字体只要还承载了正文、标题、字母或其他语言文字，就必须返回字体映射对象，无需再单独判断其中的标点。

#### 五、不得依据字体名称直接判断

不得仅凭字体名称判断它是文字字体还是符号字体。

即使字体名称中包含 `Symbol`、`Dingbats`、`Icon`、`Math`、`Unknown`，也必须查看该映射键实际承载的字符和对应页面。

反过来，即使字体名称看起来是普通正文字体，如果它在当前全部相关页面中实际只承载通用符号或纯数字，也可以返回 null。

判断对象始终是：

“当前映射键对应的字体实际承载了什么字符。”

而不是：

“这个字体的名称看起来像什么。”

### null 的证据范围

本轮返回 null，只表示：

“在当前已经提供的全部相关页面中，该字体实际承载的内容全部都是非语言的通用数字、数学符号、图形符号、图标或特殊字形，尚未发现语言文字。”

本轮 null 不代表该字体在整本 PDF 中已经最终确定不需要映射。

如果该字体在整本 PDF 中还有其他尚未提供的出现页面，程序会继续选择并提供补充页面。

只有程序检查完该字体在整本 PDF 中的全部出现页面，并且每一轮都没有发现语言文字时，程序才会把它确定为最终 null。

因此：

- 只根据当前已经提供的全部相关证据判断；
- 当前证据中出现语言文字，立即返回字体映射对象；
- 当前证据中全部为非语言通用符号或纯数字，返回 null；

### 页面与字体对应关系

同一页面可能包含多个字体。判断时必须区分不同的映射键，只根据当前映射键对应字体实际承载的内容作出决定。

不得因为页面上存在正文，就把该页所有字体都判定为非 null。

也不得因为页面上存在数学符号，就把该页所有字体都判定为 null。

请综合使用以下证据识别字体对应的内容：

- 字体清单中的实际原文样例；
- 样例所在页码；
- 字号；
- bbox 位置；
- 字体名称；
- 字体粗细、斜体、等宽、衬线等属性提示；
- 代表单页 PDF 中的实际视觉内容。

其中字体名称和属性只能作为辅助证据，实际承载的字符才是最终分类依据。

### 中文字体选择要求

对于需要返回字体映射对象的原始字体，请遵守以下要求：

1. 目标字体必须能够显示常用简体中文。
2. 目标字体应尽量与原英文字体的视觉风格、笔画重量、宽窄感和排版用途相近。
3. 正文、标题、粗体、斜体、窄体、等宽字体等不同用途应尽可能匹配。
4. 目标中文字体还应与可能保留的原英文、数字、型号和符号在同一行中视觉协调。
5. 为保证字体资源可以由当前工具环境真实获取并完成验证，正常映射所使用的目标字体必须从 `google/fonts` 仓库 `main` 分支中选择，并且必须能够通过下述 Google Fonts 字体获取工具取得真实字体文件。
6. 可以先通过网络搜索、Google Fonts、GitHub 页面、字体资料等搜索和比较候选字体，但网络资料、字体名称、网页预览或介绍页面只能作为候选筛选依据，不能替代真实字体文件获取、实际视觉分析和本地校验。
7. 最终 `download_url` 必须是可以直接获得真实字体二进制文件的公网 HTTP(S) 地址，不得指向字体介绍页、HTML 页面、Bridge 页面、Base64 文本结果页面或需要人工确认的下载页面。
8. 对通过 Google Fonts 字体获取工具取得的字体，最终 `download_url` 必须使用该字体 metadata 中的 `source_url`。
9. `GET_BASE64` 返回的是字体文件的 Base64 文本，`GET_BASE64` 对应的 URL 只是 Base64 结果地址，不是最终字体二进制下载地址，不得写入 `download_url`，也不得写入最终 `curl.exe` 命令。
10. 不同原始字体可以映射到同一个目标字体文件。
11. 同一个原始字体即使在不同页面中用途略有差异，也必须综合考虑，并只保留一个全书统一的映射结果。
12. 已经是中文字体的原字体，也可以映射到合适的统一中文字体。
13. 返回字体映射对象时，应确认目标字体文件能够实际打开，并包含常用简体中文字形。
14. 字体文件统一保存到相对路径：`.\resources\fonts\字体文件名`。
15. 不同内容的字体文件不得使用相同的目标文件名。
16. 本任务正常映射使用的目标字体文件扩展名只能是 `.otf` 或 `.ttf`。即使 Bridge 浏览页面能够显示 `.ttc`、`.woff`、`.woff2` 等其他字体资源，也不得将这些格式用于本任务的最终映射。
17. `target_font_file` 应使用 Google Fonts 字体获取工具返回的 metadata 中的 `filename`。如果原始 `google/fonts` 文件名包含当前下载环境不适合直接保存的字符，而 metadata 已给出安全文件名，应使用 metadata 的文件名，不得自行另起不一致的文件名。
18. `download_url` 必须与对应 `curl.exe` 下载命令使用的 URL 完全一致。
19. 最终输出中的 `curl.exe` 规则只约束生产环境后续直接下载字体的命令，不限制当前模型为了验证字体而通过 Google Fonts 字体获取工具取得 Base64、将该 Base64 响应完整保存为本地文本文件，并在 Python 中解码得到字体文件。
20. 当前模型在验证阶段不得绕过 Google Fonts 字体获取工具，直接从 metadata `source_url`、`final_url`、raw GitHub URL、CDN URL 或其他字体二进制直链下载候选字体作为本地校验文件。验证阶段必须以通过规定流程取得的完整 `GET_BASE64` 内容解码出的文件为准。
21. 目标字体必须通过下述“强制字体本地校验”，否则不得出现在正常映射中。
22. 不得依赖生产阶段无法明确设置的字体可变轴来模拟粗体、窄体或其他款式。如果候选是 Variable Font，而当前实际写入方式不能可靠控制其 `wght`、`wdth`、`ital` 等轴，则必须以该字体文件在实际 PyMuPDF 写入方式下呈现的真实效果判断，不得假设生产环境会自动使用所期望的可变轴实例。

### Google Fonts Bridge 固定接口事实

本任务使用的 Google Fonts 字体获取工具固定入口为：

`https://github-font-bridge.2848723598.workers.dev/browse/`

该 Bridge 的实际接口行为如下，执行时必须按照这些事实处理，不得自行假设其他返回格式。

#### 一、字体来源和文件范围

1. Bridge 浏览的字体仓库固定为：

   - owner：`google`
   - repository：`fonts`
   - ref：`main`

2. Bridge 页面会列出仓库中的若干字体格式，但本任务最终候选只允许选择 `.ttf` 或 `.otf`。

3. 字体源文件的最大允许大小为：

   `73400320` bytes

   即 70 MiB。

4. 单个候选字体超过此大小时，属于该候选无法通过本工具取得，不代表整个字体获取工具或本地校验环境系统性不可用。

#### 二、GET_METADATA 的真实响应

Action 成功完成后，状态页面会提供实际可点击的 `GET_METADATA` 链接。

`GET_METADATA` 正常响应为 JSON，至少包含以下字段：

- `source_url`
- `final_url`
- `filename`
- `output_key`
- `size_bytes`
- `sha256`
- `detected_format`
- `content_type`
- `base64_file`
- `base64_size_bytes`

其中本任务最终映射和校验直接依赖：

- `source_url`
- `final_url`
- `filename`
- `size_bytes`
- `sha256`
- `detected_format`

不得仅因为 HTTP 状态为 200 就认为 metadata 获取成功。

必须实际确认：

- 响应能够作为 JSON 解析；
- 上述必需字段真实存在；
- `filename` 非空；
- `source_url` 为 HTTPS URL；
- `size_bytes` 为合理的正整数；
- `sha256` 为实际返回的 SHA256；
- 响应不是 Bridge 错误 HTML 页面。

#### 三、GET_BASE64 的真实响应

Action 成功完成后，状态页面会同时提供实际可点击的 `GET_BASE64` 链接。

`GET_BASE64` 正常响应具有以下固定性质：

1. HTTP body 本身就是字体文件的完整 Base64 文本。
2. 正常 Content-Type 为：

   `text/plain; charset=utf-8`

3. 正常 Base64 响应没有 JSON 包装、HTML 包装、`<pre>` 包装或其他业务字段。
4. Base64 内容由 Python `base64.encode()` 根据真实字体二进制生成，因此其中正常包含 ASCII 换行。
5. Base64 文本末尾存在正常换行不属于错误。
6. `GET_BASE64` URL 是普通公开 GET 地址，请求该 URL 不需要模型携带 GitHub Token、浏览器 Cookie 或此前浏览产生的会话状态。GitHub Token 仅由 Bridge Worker 在服务器端访问 GitHub 时内部使用。
7. 因此，一旦已经通过页面实际点击流程取得合法的 `GET_BASE64` URL，如果网页正文读取能力无法完整返回大型 Base64，就可以使用当前环境的 URL→本地文件保存能力，把该实际 URL 的完整 HTTP 响应直接保存为本地 `.txt` 或 `.b64` 文件，再让 Python 直接读取。

#### 四、Bridge 错误页的 HTTP 状态注意事项

Bridge 为兼容部分受限网页客户端，很多错误页面也会故意返回 HTTP 200。

因此：

**HTTP 200 本身绝不构成成功证据。**

例如以下情况可能仍以 HTTP 200 返回 HTML 错误页面：

- 字体不存在；
- 路径无效；
- GitHub API 出错；
- Action 无法 dispatch；
- 并发额度已满；
- 每日额度已满；
- result 文件尚不存在；
- result 获取失败；
- GitHub Token 或上游服务异常；
- 其他 Bridge 内部错误。

因此必须检查实际页面或响应内容。

对于 `GET_METADATA`：

- 必须实际解析出有效 metadata JSON；
- 如果得到 HTML、ERROR 页面、空内容或不符合字段要求的内容，则该次 metadata 获取失败。

对于 `GET_BASE64`：

- 必须确认保存的是完整纯 Base64 正文；
- 如果得到 HTML、ERROR 页面、状态页面、JSON 错误对象、空内容或其他非 Base64 内容，则该次 Base64 获取失败。

不得使用“HTTP 200”替代真实内容验证。

#### 五、Base64 本地解码规则

取得完整 `GET_BASE64` 响应后，必须由 Python 在本地完成解码。

允许的处理只有：

- 忽略 ASCII 空格；
- 忽略 `\r`；
- 忽略 `\n`；
- 忽略 `\t`；
- 忽略其他标准 ASCII whitespace。

去除上述 ASCII whitespace 后，必须对剩余内容执行严格 Base64 解码。

不得：

- 猜测被截断的内容；
- 自动修复缺失的 Base64 数据；
- 删除任何非空白 Base64 字符；
- 修改任何非空白 Base64 字符；
- 替换无法识别的字符；
- 根据文件头反推并补写 Base64；
- 对不完整 Base64 强行补全后继续校验。

如果严格 Base64 解码失败，应判定本次字体获取失败。

解码成功后，还必须使用 metadata 的 `size_bytes` 和 `sha256` 对真实解码文件进行双重确认。

只有：

- Base64 完整解码成功；
- 文件大小与 metadata `size_bytes` 完全一致；
- 本地重新计算 SHA256 与 metadata `sha256` 完全一致；

才说明通过 Bridge 得到的真实字体文件字节已经可靠恢复。

#### 六、Action 状态与刷新语义

Bridge 中不同状态必须按实际含义处理。

以下状态表示已经有 Action 被 dispatch，或者已经进入对应 Action 的定位/执行流程：

- `ENCODE_QUEUED`
- `ENCODE_DISPATCHED`
- `WORKFLOW_RUN_FOUND`
- `WAITING_FOR_WORKFLOW_RUN`
- `queued`
- `in_progress`
- `PENDING`

遇到这些状态时，应继续使用页面实际提供的链接，例如：

- `CHECK_STATUS`
- `FIND_WORKFLOW_RUN`
- `OPEN_STATUS`
- `REFRESH_RUN_DISCOVERY`
- `REFRESH_STATUS`

直到 Action 明确：

- `SUCCESS`
- 或 `FAILED`

不得自行构造 run ID、output key、status URL 或 result URL。

特别注意：

`too_many_active_runs` 和 `daily_limit_reached` 与上述状态不同。

它们发生在新的 Action dispatch 之前，因此本次请求没有新建可供刷新的 run。

##### `too_many_active_runs`

出现 `too_many_active_runs` 时：

- 表示当前活动 Action 数量达到 Bridge 的并发限制；
- 当前这次 `ENCODE_THIS_FONT` 没有成功创建新的 run；
- 不存在本次请求对应的 `CHECK_STATUS` 或 `REFRESH_STATUS`；
- 不得自行编造 run ID 或 status URL；
- 后续只有在并发限制已经解除后，重新通过页面实际流程进入该字体并重新点击 `ENCODE_THIS_FONT`，才能重新发起获取。

单次遇到 `too_many_active_runs` 不代表该字体失败，也不立即代表整个工具系统性不可用。

但是，如果在当前任务可用的实际操作范围内持续受此限制，导致本轮无法通过规定流程取得任何完成正常映射所需要的字体文件，则可以按照“字体获取工具系统性不可用”的规则处理。

##### `daily_limit_reached`

出现 `daily_limit_reached` 时：

- 表示当天新的 Action dispatch 数量已经达到 Bridge 的每日限制；
- 当前这次请求没有成功创建新的 run；
- 不存在本次请求对应的可刷新 Action；
- 不得自行构造 run ID、status URL 或 result URL。

如果已有此前在本轮成功完成并已经取得完整 Base64 的字体资源，可以继续使用那些已经真实取得并验证的资源。

如果每日限制导致本轮无法取得任何完成正常映射所必需的新字体文件，则属于本轮字体获取工具实际不可用，可以按照 `[本地无校验工具]` 的特殊出口处理。

### 强制字体本地校验

本任务选择的目标字体将由生产环境中的 PyMuPDF 写入 PDF 原生文本。

目标字体不仅必须能显示中文，还必须保证写入 PDF 后可以按原始标准 Unicode 码位搜索、复制和提取。

禁止仅根据字体名称、字体官网、开源许可证、支持中文的说明、网络评价、网页预览或个人经验断定字体合格。

在正常输出任何字体映射之前，必须亲自使用工具完成以下检查。

某个候选字体检查失败时，应在本轮内部放弃该候选并继续寻找、获取和测试其他候选字体；不得因为一个候选字体失败就输出特殊标记。

#### 一、校验环境

必须具备以下本地能力：

1. 可以执行 Python；
2. 可以访问本任务提供的 Google Fonts 字体获取工具；
3. 可以通过该工具取得 metadata；
4. 可以通过该工具取得完整 `GET_BASE64` 响应，或者能够将页面实际提供的 `GET_BASE64` URL 对应的完整 HTTP 响应原样保存为本地 Base64 文本文件；
5. 可以由 Python 读取完整 Base64 内容并解码为真实字体文件；
6. 可以读取和写入临时文件；
7. 可以导入并运行 PyMuPDF；
8. 可以导入并运行 fontTools；
9. 可以创建、保存、重新打开临时 PDF；
10. 可以从重新打开的 PDF 中提取文本；
11. 可以读取字体的全部 Unicode cmap 表；
12. 可以把本地生成的字体视觉测试结果实际渲染出来并进行视觉检查。

生产环境使用的 PyMuPDF 版本为：

`{pymupdf_version}`

必须使用与上述版本完全一致的 PyMuPDF 完成测试。

当前环境版本不同但允许安装依赖时，应先安装指定版本后再测试；不得仅凭其他版本的结果推断。

如果当前工具环境确实无法执行 Python、无法安装或运行指定版本 PyMuPDF、无法运行 fontTools、无法访问临时文件系统、无法真实执行下述测试，或者 Google Fonts 字体获取工具发生系统性不可用并导致无法真实取得任何准备使用的字体文件，则不得猜测通过，必须按特殊协议输出 `[本地无校验工具]`。

这里所说的 Google Fonts 字体获取工具“系统性不可用”包括但不限于：

- 无法打开字体获取工具入口；
- 无法正常浏览 `google/fonts` 目录；
- 无法触发字体编码 Action；
- Action 服务持续不可用；
- 服务配额或并发限制导致本轮无法取得任何所需字体；
- Action 已成功但无法取得 metadata；
- Action 已成功但既无法通过网页读取取得完整 Base64，也无法通过当前工具环境的 URL→本地文件保存能力，将页面实际提供的 `GET_BASE64` URL 对应的完整 HTTP 响应保存为本地文本文件；
- 当前工具只能取得被截断、摘要化、预览化或明显不完整的 Base64，并且不存在可用的完整响应落盘路径；
- 已经取得完整 Base64，但 Base64 无法在本地可靠解码为完整文件；
- 解码后的文件大小或 SHA256 持续无法与 metadata 对应；
- 当前工具环境无法实际查看本地渲染结果，因此不能完成要求的真实视觉判断。

特别注意：

普通网页读取接口因为响应体过大、上下文长度限制、网页正文长度限制或类似原因，不能直接显示完整 `GET_BASE64` 内容，本身不属于字体获取工具系统性不可用。

只要已经通过页面实际提供的链接取得合法的 `GET_BASE64` URL，并且当前工具环境能够把该 URL 对应的 HTTP 响应完整保存为本地文本文件，就必须使用该落盘方式继续后续 Python 解码，不得仅因为网页正文无法完整展示 Base64 就输出 `[本地无校验工具]`。

这种 URL→本地文件保存能力只允许用于保存通过规定页面流程实际取得的 `GET_BASE64` 文本响应，目的是避免大型 Base64 内容经过模型上下文传输时被截断。

不得利用该能力绕过 Bridge，直接下载 `source_url`、`final_url` 或其他字体二进制直链作为验证字体。

单个候选字体不存在、获取失败、字体过大、字体文件损坏、缺字、视觉不匹配、cmap 检查失败或 PyMuPDF 往返失败，不属于系统性工具不可用。

遇到这种情况必须放弃该候选并继续寻找其他候选字体。

#### 二、代表 PDF 下载检查

必须亲自下载并使用 PyMuPDF 打开本轮列出的全部相关单页 PDF。

每个文件必须：

- 下载成功；
- 文件非空；
- 能被 PyMuPDF 正常打开；
- 恰好包含一页；
- 可以读取页面尺寸；
- 可以查看该页的实际视觉内容。

如果任意相关单页 PDF 无法下载、为空、不是有效 PDF、无法打开或不是单页，不得根据字体清单、文字样例、文件名、截图缓存或猜测输出映射，必须按特殊协议输出 `[无法下载PDF]`。

#### 三、Google Fonts 字体获取

需要获取真实目标字体文件时，必须使用以下固定入口：

`https://github-font-bridge.2848723598.workers.dev/browse/`

对准备写入最终映射的每一个不同目标字体文件，必须完成以下流程。

1. 先结合本轮代表 PDF 的实际视觉内容、字体清单、文字样例、字号、bbox、粗细、斜体、窄体、等宽和衬线提示，在网络上搜索、比较并确定一个或多个候选字体。

2. 候选字体必须来自 `google/fonts` 的 `main` 分支。

   必须确认准确的 `.ttf` 或 `.otf` 仓库路径，不得仅凭记忆猜测文件路径。

   即使 Bridge 页面能够显示 `.ttc`、`.woff`、`.woff2` 等其他格式，本任务也不得将这些格式作为最终候选字体。

3. 打开固定入口：

   `https://github-font-bridge.2848723598.workers.dev/browse/`

4. 根据已确定的候选路径，通过页面实际 HTML 链接逐层点击目录、`PREFIX`、`[FONT]` 和 `ENCODE_THIS_FONT`。

5. 必须以页面实际提供的可点击链接为准。

   不得绕过页面流程自行猜测或构造 `/encode/`、`/locate/`、`/status/` 或 `/result/` 内部 URL，也不得自行编造 `run_id`、`output_key` 或其他内部参数。

6. 触发字体编码后，根据页面实际提供的链接继续执行：

   - `CHECK_STATUS`
   - `FIND_WORKFLOW_RUN`
   - `OPEN_STATUS`
   - `REFRESH_RUN_DISCOVERY`
   - `REFRESH_STATUS`

   中实际存在且适用于当前状态的操作，直到对应 Action 明确完成。

7. 如果状态仍是：

   - queued；
   - in_progress；
   - pending；
   - `PENDING`；
   - `WAITING_FOR_WORKFLOW_RUN`；

   不得假定成功，必须继续通过页面实际提供的检查或刷新链接处理。

8. 如果出现 `too_many_active_runs`，必须理解为本次 Action 尚未 dispatch。

   此时不得尝试刷新不存在的本次 run，不得自行构造 status URL。

   如果当前操作条件下限制解除，可以重新通过页面实际流程点击 `ENCODE_THIS_FONT`。

   如果持续受此限制并导致本轮无法取得任何完成正常映射所需字体，才可按照字体获取工具系统性不可用处理。

9. 如果出现 `daily_limit_reached`，必须理解为本次 Action 尚未 dispatch。

   不得自行构造 run。

   如果该限制导致本轮无法取得任何完成正常映射所必需的新字体，则可以按照字体获取工具系统性不可用处理。

10. Action 明确成功后，必须同时取得：

   - `GET_METADATA`
   - `GET_BASE64`

11. `GET_METADATA` 中至少应取得并记录：

   - `source_url`
   - `final_url`
   - `filename`
   - `size_bytes`
   - `sha256`
   - `detected_format`

12. 不得仅根据 HTTP 200 判断 `GET_METADATA` 成功。

   必须实际确认响应是有效 JSON，而不是 Bridge 的 HTTP 200 错误 HTML 页面。

13. `GET_BASE64` 返回的是完整字体二进制文件经过 Base64 编码后的纯文本响应。

   正常响应正文没有 JSON、HTML 或 `<pre>` 包装。

   该文本可能非常大，并且正常包含 ASCII 空白和换行；不得因为 Base64 中存在换行就认为内容无效。

14. 必须取得完整 Base64 内容。

   不得只复制网页中可见的一小段、摘要、预览、开头、结尾或截断后的内容。

15. 获取完整 Base64 时，允许且应根据当前工具能力采用以下两种方式之一：

   - 如果网页读取能力能够完整返回 `GET_BASE64` 的全部响应正文，可以将完整正文交给 Python；
   - 如果网页读取能力因为响应体过大、正文长度限制或上下文限制而无法完整返回内容，则必须使用当前环境可用的 URL→本地文件保存能力，将通过页面实际链接取得的 `GET_BASE64` URL 对应的完整 HTTP 响应原样保存为本地文本文件，再由 Python 直接读取该本地文本文件。

16. 使用 URL→本地文件方式保存 Base64 时，必须遵守以下要求：

   - URL 必须是按照上述页面实际点击流程取得的真实 `GET_BASE64` URL；
   - 不得自行猜测、拼接或构造 `GET_BASE64` URL；
   - 保存目标应是临时文本文件，例如 `.txt` 或 `.b64`；
   - 必须保存完整 HTTP 响应正文，不得保存网页摘要、截断文本、截图、HTML 预览片段或模型转述内容；
   - 正常 GET_BASE64 body 应为纯 Base64 文本；
   - 如果下载或保存后的内容实际是 HTML 错误页、状态页、权限页、JSON 错误内容或其他非 Base64 内容，应判定该次获取失败；
   - 不得因为保存请求返回 HTTP 200 就假定内容有效；
   - 不得把 metadata 的 `source_url`、`final_url`、GitHub raw 地址或其他字体二进制直链交给这种本地下载能力来绕过 Base64 流程。

17. 普通网页读取 `GET_BASE64` 时出现“内容过大”“无法完整读取”“超过正文长度限制”或类似错误，只要页面实际取得的 `GET_BASE64` URL 仍然可以通过本地文件保存能力完整保存，就不是候选失败，也不是工具系统性不可用。

18. 必须使用 Python 在本地将完整 Base64 解码为字体文件。

   完整 Base64 可以来自网页完整正文，也可以来自上述本地 `.txt` / `.b64` 文件。

19. Python 解码前只能按照标准 Base64 规则忽略 ASCII whitespace，包括空格、回车、换行和制表符。

   去除 ASCII whitespace 后，必须执行严格 Base64 解码。

   不得修改、删除、替换、猜测、补写、修复或重新编码任何非空白 Base64 字符。

20. 如果使用本地 Base64 文本文件，Python 必须直接读取该完整文件进行解码，不得先把全文重新输出到模型上下文、终端显示或其他可能截断内容的中间通道。

21. 解码完成后必须重新检查：

   - 本地字体文件真实存在且非空；
   - 本地字体文件大小与 metadata 的 `size_bytes` 完全一致；
   - 对本地字体文件重新计算 SHA256；
   - 本地 SHA256 与 metadata 的 `sha256` 完全一致。

22. 只有 Base64 解码成功、文件大小一致且 SHA256 一致，才算真实取得了该字体文件。

23. 随后必须使用 fontTools 实际打开该字体文件，并使用 PyMuPDF 实际打开或加载该字体文件。

   仅成功完成 Base64 解码不足以证明它是有效字体。

24. metadata 中的 `source_url` 才是后续生产环境直接下载该字体文件时使用的公网 URL。

   最终字体映射对象中的 `download_url`、字体本地校验报告中的 `download_url` 和最终 `curl.exe` 命令中的 URL 必须全部使用完全相同的 metadata `source_url`。

25. `GET_BASE64` 对应的 Bridge URL、`GET_METADATA` 对应的 Bridge URL、`/font/`、`/encode/`、`/status/`、`/locate/` 和 `/result/` URL 都不得出现在最终字体映射的 `download_url` 中。

26. metadata 中的 `final_url` 只用于核实该次 Action 实际完成下载后的最终网络位置。

   除非本任务协议另有明确要求，否则最终映射仍必须使用 metadata 的 `source_url`，不得自行把 `final_url` 替换为 `download_url`。

27. 同一个真实字体文件在本轮只需要获取和完整验证一次。

   如果多个映射键最终使用同一个目标字体文件，应复用已经验证的本地文件及其 metadata，不得为完全相同的字体重复触发 Action。

28. 不要为了浏览字体而无目的地大量触发 Action。

   网页搜索、字体资料和 Google Fonts 页面可以先用于筛选；只有准备进入真实视觉比较或最终校验的候选才需要触发字体获取。

只有真实取得完整 Base64、成功解码得到真实字体文件、文件大小与 metadata 一致、SHA256 与 metadata 一致，并且字体能够成功解析，才算候选字体获取成功。

#### 四、真实字体视觉分析

在候选字体通过上述文件真实性检查后，必须进行实际视觉分析。

不得仅因为某字体名称中含有 Sans、Serif、Mono、Bold、Condensed、Italic 等词，就认为它与原字体视觉匹配。

对每一个准备最终使用的目标字体，必须至少完成以下步骤：

1. 实际查看该原始字体所在的全部相关代表 PDF 页面。

2. 根据字体清单中的页码、字号、bbox 和文字样例，定位该映射键在代表页面中的实际文字，并判断它在页面中的真实排版用途，例如：

   - 正文；
   - 一级或二级标题；
   - 表格标题；
   - 表格正文；
   - 图注；
   - 脚注；
   - 页眉页脚；
   - 粗体强调；
   - 斜体说明；
   - 窄体标签；
   - 等宽代码或寄存器文本。

3. 使用已经通过完整 Base64 解码、文件大小检查和 SHA256 检查的真实候选字体文件，在本地生成实际渲染结果。

4. 视觉测试不得只渲染单个汉字。

   测试内容应同时包含中文以及本书中可能保留的英文、数字、型号、单位、寄存器名、引脚名和技术缩写。

至少应包含类似以下中英混排内容：

`中文电源电压监控保护绝对最大额定值技术数据手册 BQ769x0 ADC I²C GPIO1 R12 VIN VOUT 3.3 V ±25 ℃ 10 kΩ`

并应根据当前映射键的实际原文样例补充具有代表性的文本。

5. 应尽量按照原字体在代表 PDF 中的实际字号和用途生成候选字体视觉样例；如果一个字体在多个字号中出现，可以选择最有代表性的字号，并结合其他字号判断。

6. 必须实际查看本地生成的渲染结果，而不是仅成功生成文件后就认为视觉检查完成。

7. 将候选字体渲染结果与相关代表 PDF 中的原文字体进行视觉比较，至少判断以下方面：

   - 整体字面大小；
   - 笔画粗细；
   - 页面视觉黑度；
   - 横向宽度；
   - 紧凑或舒展程度；
   - 字符间整体节奏；
   - 衬线或无衬线特征；
   - 等宽或比例字体特征；
   - 粗体强调程度；
   - 斜体或倾斜感；
   - 窄体或压缩感；
   - 标题、正文、表格、注释等实际用途是否协调；
   - 中文与保留英文、数字、型号、单位和技术缩写混排时是否协调。

8. 如果候选字体虽然支持中文且技术校验可以通过，但视觉风格与原字体明显不协调，应放弃该候选并继续寻找其他候选。

9. 如果多个候选在技术上都合格，应通过真实视觉比较选择更接近原字体实际用途的候选，不得随机选择。

10. 如果多个原始字体本来具有明显不同的视觉用途，例如正文 Regular、标题 Bold、窄体标签、等宽代码，不应仅为了减少字体文件数量而强行把它们全部映射到视觉上明显相同的一个字体文件。

11. 反过来，如果多个原始字体在实际页面中的用途和视觉效果相近，允许映射到同一个经过验证的目标字体文件。

12. 对 Variable Font，不得仅凭字体支持某个 `wght`、`wdth`、`ital` 等轴就假定生产环境会按所需轴值使用。

   视觉判断必须基于当前实际写入方式能够得到的真实字体效果。

13. 真实视觉比较只能用于决定“哪个技术上合格的字体更适合映射”，不能替代下面的 Unicode cmap 扫描和 PyMuPDF 精确往返测试。

#### 五、候选字体结构和字符覆盖检查

对准备写入最终映射的每一个不同目标字体文件，在完成真实字体获取和视觉比较后，还必须确认：

- Base64 来源是通过规定 Google Fonts Bridge 页面流程实际取得的 `GET_BASE64` 内容；
- 如果通过 URL→本地文件方式保存 Base64，保存使用的是页面实际提供的 `GET_BASE64` URL，而不是自行构造的 URL；
- 解码结果不是 HTML、错误页面、Base64 截断内容或其他非字体文件；
- 文件大小与 metadata 完全一致；
- SHA256 与 metadata 完全一致；
- 字体文件可以由 PyMuPDF 打开或加载；
- 字体文件可以由 fontTools 打开；
- 字体包含本任务固定测试字符串中的全部字符；
- 计算并记录真实文件的 SHA256 和文件大小。

某个候选字体无法获取、无法打开、缺字或视觉不合适时，应放弃该候选并继续寻找其他字体，不得把未完成校验的字体写入最终映射。

不得因为某一个候选字体获取失败就立即输出 `[本地无校验工具]`。

不得因为普通网页读取接口无法直接展示完整大型 Base64 就立即输出 `[本地无校验工具]`；如果能够将页面实际提供的 `GET_BASE64` URL 对应响应完整保存到本地文件，就必须继续执行。

只有在已经确认是当前字体获取工具或本地工具环境的系统性问题，并导致无法通过：

`Bridge → GET_BASE64 → 完整响应落盘或读取 → Python 解码`

的规定路径取得任何可用于完成正常映射的字体时，才允许使用 `[本地无校验工具]`。

#### 六、完整 cmap 歧义扫描

必须使用 fontTools 读取候选字体的全部 Unicode cmap 子表，并建立：

- Unicode 码位 -> 字形；
- 字形 -> 该字形对应的全部 Unicode 码位。

必须完整识别同时满足以下条件的字形：

- 至少对应一个 CJK 统一表意文字；
- 同时对应一个 CJK 兼容表意文字（U+F900–U+FAFF 或 U+2F800–U+2FA1F）。

不得只抽查“器、不、量、年”等少数字符。

必须收集该字体中全部此类字形对应的标准 CJK 统一表意文字，把这些标准字符全部加入 PyMuPDF 精确往返测试集合。

`cmap` 中存在这种共享字形并不自动判定失败；它表示这些字符必须全部经过真实 PyMuPDF 往返测试。

最终是否通过，只能由下面的逐码位精确往返结果决定。

#### 七、PyMuPDF 精确往返测试

必须使用与生产阶段相同的关键调用方式生成临时 PDF：

- `page.insert_font(..., set_simple=False)`；
- 分别使用 `page.insert_text()` 和 `page.insert_textbox()`；
- `doc.subset_fonts(fallback=True)`；
- `doc.save(..., garbage=4, deflate=True)`；
- 保存后重新打开 PDF；
- 使用 PyMuPDF 提取页面文本。

测试集合至少包括：

1. 完整 cmap 扫描发现的全部“标准/兼容码位共享字形”对应的标准汉字；
2. `中文电源电压监控保护绝对最大额定值技术数据手册`；
3. `器不量年行更路料串理便利`；
4. `控制器寄存器转换器驱动器`；
5. `测量数量容量电量`；
6. `不能不同不使用不连接`；
7. `年月更新执行管理系列`；
8. 中文、拉丁字母、数字、单位、标点和技术缩写混合文本，包括 `BQ769x0`、`ADC`、`I²C`、`3.3 V`、`GPIO1`、`R12`、`VIN`、`VOUT`、`表1（测试）`、`±25 ℃`、`10 kΩ`。

`insert_text()` 和 `insert_textbox()` 必须分别完成完整测试；两者都必须经过字体子集化和重新打开后的文本提取。

输入字符串和提取字符串必须未经 NFC、NFKC 或其他 Unicode 归一化，直接逐码位完全一致。

不得只比较视觉字形，不得把兼容汉字视为与标准汉字相同，不得忽略任何不同字符。

只要出现以下任一情况，该候选字体即为失败：

- 输入字符与提取字符不完全相同；
- 提取结果含 U+F900–U+FAFF；
- 提取结果含 U+2F800–U+2FA1F；
- `insert_text()` 测试失败；
- `insert_textbox()` 测试失败；
- 字体子集化失败；
- 保存、重新打开或提取临时 PDF 失败。

失败候选不得出现在正常映射或校验报告的 `pass` 项中，必须继续寻找并测试其他字体。

#### 八、正常输出条件

只有满足以下全部条件时，才允许正常输出字体映射：

1. 已下载并检查全部相关单页 PDF；
2. 具备指定版本的 PyMuPDF 和可工作的 fontTools；
3. 映射引用的每一个不同字体文件均来自 `google/fonts` `main` 分支；
4. 映射引用的每一个不同字体文件扩展名均为 `.ttf` 或 `.otf`；
5. 映射引用的每一个不同字体文件均已通过规定的 Google Fonts 字体获取工具实际取得；
6. 每一个字体均已取得 metadata 和完整 `GET_BASE64` 内容；
7. 已确认 metadata 实际为有效 JSON，而不是 HTTP 200 的 Bridge 错误 HTML 页面；
8. 如果网页读取不能完整展示 `GET_BASE64`，已经使用页面实际提供的 `GET_BASE64` URL 将完整响应原样保存为本地 Base64 文本文件，而不是使用截断网页正文；
9. 已确认 GET_BASE64 本地保存结果实际为纯 Base64 文本，而不是 HTTP 200 的 HTML 错误页、状态页或其他错误内容；
10. 每一个字体均已把完整 Base64 在本地通过 Python 解码为真实字体文件；
11. 每一个解码字体的文件大小均与 metadata 的 `size_bytes` 完全一致；
12. 每一个解码字体重新计算的 SHA256 均与 metadata 的 `sha256` 完全一致；
13. 每一个最终字体都已经使用真实字体文件生成视觉测试结果并实际完成视觉比较；
14. 最终选择的字体在视觉上与原字体的实际用途合理协调；
15. 每一个字体均已完成全部 Unicode cmap 扫描；
16. 每一个字体均通过 `insert_text()` 精确往返测试；
17. 每一个字体均通过 `insert_textbox()` 精确往返测试；
18. 每一个测试均执行了 `subset_fonts(fallback=True)`；
19. 提取结果中不存在 CJK 兼容表意文字；
20. 校验报告中的文件名、URL、SHA256、文件大小与最终映射和下载命令完全一致；
21. 最终映射和下载命令中的 URL 使用 metadata 的 `source_url`，而不是任何 Bridge Base64、metadata、status 或其他内部 URL；
22. 当前模型本地校验使用的字体文件确实来自规定 Bridge 流程返回的完整 Base64 解码结果，而不是绕过 Bridge 从 `source_url`、`final_url` 或其他字体二进制直链直接下载所得。

不得声称某字体“理论上应该通过”。

不得把网络资料、字体介绍、Google Fonts 网页预览、GitHub 页面、字体名称或经验判断当成本地校验结果。

不得仅因为成功取得 Base64 就声称字体已经通过。

不得仅因为 Base64 已经完整保存到本地就声称字体已经通过。

不得仅因为 SHA256 与 metadata 一致就跳过视觉分析、cmap 扫描或 PyMuPDF 精确往返测试。

不得因为普通网页读取无法直接显示大型 Base64 就声称字体获取工具不可用；只要可以通过页面实际提供的 `GET_BASE64` URL 完整落盘，就必须继续正常流程。

### 映射完整性要求

1. 必须为“本轮待处理字体清单”中的每一个映射键返回且只返回一个结果。
2. `mappings` 的键集合必须与本轮字体清单中的映射键集合完全一致。
3. 不得返回本轮字体清单之外的字体，包括之前已经得到字体映射对象的字体。
4. 不得修改映射键的拼写、大小写或字符。
5. 不得合并多个映射键。
6. 每个映射值只能是一个字体映射对象或 JSON null。
7. 字体映射对象只能包含 `target_font_file` 和 `download_url` 两个字段。
8. 不得增加 `reason`、`action`、`description`、`confidence`、`evidence`、`base64`、`bridge_url`、`metadata_url`、`source_path`、`output_key`、`final_url` 或任何其他字段。
9. 即使无法完全确定最佳目标字体，也必须按照现有证据选择最合适且已经完成真实获取、视觉分析和本地校验的字体，不得输出协议外的说明。
10. 返回 null 的字体不得生成字体下载命令，也不得出现在字体校验报告的 `fonts` 中。
11. 非 null 映射的 `target_font_file` 必须与该字体 metadata 中的 `filename` 一致。
12. 非 null 映射的 `download_url` 必须与该字体 metadata 中的 `source_url` 一致。
13. 非 null 映射的 `target_font_file` 扩展名只能为 `.ttf` 或 `.otf`。
14. Bridge 返回的 Base64 内容只用于当前模型工具环境恢复真实字体文件，不得写入最终 JSON。
15. Bridge 的任何 `/browse/`、`/font/`、`/encode/`、`/locate/`、`/status/` 或 `/result/` URL 均不得作为最终 `download_url`。
16. 用于完整保存大型 Base64 响应的临时本地 `.txt`、`.b64` 或其他中间文件只属于当前校验过程，不得写入最终映射 JSON、字体校验报告或生产下载命令。

### 输出协议

处理完成后，只输出以下三个区块，区块之外不得有任何内容。

每个 START 和 END 标记必须且只能出现一次。

三个区块必须按顺序紧邻输出，不得使用 Markdown 代码围栏。

#### 正常输出

[字体下载命令行 START]
（Windows PowerShell 命令，每条命令单独一行）
（只允许使用 curl.exe 下载字体文件，或使用 New-Item 创建 .\resources\fonts 目录）
（所有命令以“精翻工程\_图像处理公共资源”作为当前工作目录执行）
（curl.exe 必须使用 -o 或 --output）
（字体必须保存到 .\resources\fonts\字体文件名）
（建议使用 -L 跟随重定向）
（相同目标字体文件只下载一次）
（只为本轮返回字体映射对象的字体资源输出下载命令）
（返回 null 的字体不得输出下载命令）
（curl.exe 使用的 URL 必须是对应字体 metadata 中的 source_url）
（不得使用 GET_BASE64、GET_METADATA 或其他 Bridge URL 作为 curl.exe 下载地址）
[字体下载命令行 END]
[字体本地校验报告 START]
（这里直接输出严格 JSON，不得使用代码围栏，不得加入注释或说明）
[字体本地校验报告 END]
[字体映射表 START]
（这里直接输出严格 JSON，不得使用代码围栏，不得加入注释或说明）
[字体映射表 END]

字体本地校验报告必须严格采用以下结构；`fonts` 的键集合必须与最终映射实际引用的不同 `target_font_file` 集合完全一致：

{
  "version": 1,
  "status": "passed",
  "environment": {
    "python_version": "实际版本",
    "pymupdf_version": "{pymupdf_version}",
    "fonttools_version": "实际版本"
  },
  "fonts": {
    "目标字体文件名.otf": {
      "download_url": "https://稳定公网直接下载地址/目标字体文件名.otf",
      "sha256": "64位小写十六进制",
      "size_bytes": 123456,
      "unicode_cmap_scanned": true,
      "ambiguous_glyph_count": 0,
      "ambiguous_standard_codepoint_count": 0,
      "insert_text_exact_roundtrip": true,
      "insert_textbox_exact_roundtrip": true,
      "subset_fonts_tested": true,
      "compatibility_ideographs_found_after_extract": false,
      "result": "pass"
    }
  }
}

其中：

- `download_url` 必须等于该字体 Google Fonts Bridge metadata 中实际返回的 `source_url`；
- `sha256` 必须等于完整 Base64 解码得到的真实本地字体文件重新计算出的 SHA256，并且必须与 metadata 中的 SHA256 完全一致；
- `size_bytes` 必须等于完整 Base64 解码得到的真实本地字体文件大小，并且必须与 metadata 中的 `size_bytes` 完全一致；
- 无论完整 Base64 是由网页正文直接取得，还是通过页面实际提供的 `GET_BASE64` URL 完整保存为本地文本文件后读取，都必须以最终实际解码得到的本地字体文件为校验依据；
- HTTP 200 本身不得作为 `GET_METADATA` 或 `GET_BASE64` 成功证据。

字体映射表 JSON 必须严格采用以下结构：

{
  "version": 3,
  "mappings": {
    "原始字体映射键1": {
      "target_font_file": "目标字体文件名.otf",
      "download_url": "https://稳定公网直接下载地址/目标字体文件名.otf"
    },
    "当前证据中仅承载非语言通用符号或纯数字的字体": null
  }
}

其中正常非 null 映射：

- `target_font_file` 必须使用成功获取字体的 metadata `filename`；
- `download_url` 必须使用成功获取字体的 metadata `source_url`；
- `target_font_file` 扩展名只能为 `.ttf` 或 `.otf`。

#### 特殊出口一：无法下载 PDF

如果无法亲自下载、打开并检查任意相关单页 PDF，三个区块的内容必须且只能分别为 `[无法下载PDF]`：

[字体下载命令行 START]
[无法下载PDF]
[字体下载命令行 END]
[字体本地校验报告 START]
[无法下载PDF]
[字体本地校验报告 END]
[字体映射表 START]
[无法下载PDF]
[字体映射表 END]

#### 特殊出口二：本地无校验工具或字体获取工具系统性不可用

如果当前工具环境无法真实完成指定版本 PyMuPDF、fontTools、临时 PDF 写入、子集化、重新打开、逐码位提取测试、真实视觉查看，或者 Google Fonts 字体获取工具发生系统性不可用并导致无法通过规定的 Base64 流程取得完成正常映射所必需的真实字体文件，则三个区块的内容必须且只能分别为 `[本地无校验工具]`：

[字体下载命令行 START]
[本地无校验工具]
[字体下载命令行 END]
[字体本地校验报告 START]
[本地无校验工具]
[字体本地校验报告 END]
[字体映射表 START]
[本地无校验工具]
[字体映射表 END]

不得在特殊标记前后添加解释。

单个候选字体不存在、获取失败、Action 单次失败、字体文件过大、字体解析失败、缺字、视觉不匹配、cmap 检查失败或 PyMuPDF 往返失败不属于特殊出口；必须放弃该候选并继续寻找其他候选字体。

普通网页读取接口无法直接展示完整 `GET_BASE64` 内容，也不属于特殊出口。

只要已经通过页面实际链接取得合法 `GET_BASE64` URL，并且当前工具环境能够把该 URL 的完整 HTTP 响应保存为本地 Base64 文本文件，就必须采用该方式继续完成 Python 解码和后续校验。

只有在以下情况之一成立时，才可把“无法取得完整 Base64”计入字体获取工具系统性不可用：

- 页面流程本身无法取得合法的 `GET_BASE64` 链接；
- `GET_BASE64` 服务实际失败；
- 网页读取无法取得完整 Base64，同时当前工具环境也没有任何能力把该实际 `GET_BASE64` URL 的完整 HTTP 响应保存到本地文件；
- 本地保存得到的响应持续为截断内容、错误页、HTML 页或其他非完整 Base64；
- 当前工具环境无法让 Python 读取完整落盘的 Base64 内容并解码；
- 经过当前可用工具能力后，本轮仍无法通过规定 Base64 路径取得任何完成正常映射所需要的真实字体文件。

如果只是出现：

- `queued`
- `in_progress`
- `PENDING`
- `WAITING_FOR_WORKFLOW_RUN`

等已经存在对应 Action 或 run 定位流程的状态，并且页面仍提供合法的后续检查或刷新路径，不得把候选判为成功或伪造校验结果，也不得立即使用特殊出口。

应按照页面实际提供的：

- `CHECK_STATUS`
- `FIND_WORKFLOW_RUN`
- `OPEN_STATUS`
- `REFRESH_RUN_DISCOVERY`
- `REFRESH_STATUS`

继续完成已有流程。

如果出现 `too_many_active_runs`：

- 本次 Action 尚未 dispatch；
- 不存在本次请求对应的 run；
- 不得使用 `REFRESH_STATUS` 等方式刷新一个并不存在的 run；
- 不得自行编造 run ID、output key 或 status URL；
- 只有在并发限制解除后重新通过页面实际流程点击 `ENCODE_THIS_FONT` 才能重新发起；
- 单次出现该状态不立即构成特殊出口；
- 如果该限制在本轮实际可用操作范围内持续阻止取得任何完成正常映射所需字体，则可以按字体获取工具系统性不可用处理。

如果出现 `daily_limit_reached`：

- 本次 Action 尚未 dispatch；
- 不存在本次请求对应的 run；
- 不得自行构造 run ID 或 status URL；
- 如果已有本轮此前成功取得并完整验证的字体，可继续使用；
- 如果每日限制导致本轮无法取得完成正常映射所必需的任何新字体，则可以按字体获取工具系统性不可用处理。

### 输出前必须自行检查

输出前请逐项检查：

1. `version` 是否严格为数字 `3`。
2. `mappings` 是否为 JSON 对象。
3. `mappings` 的键集合是否与字体清单中的全部“映射键”完全一致。
4. 每个映射键是否只出现一次。
5. 是否错误地把含有英文字母、中文或其他语言文字的字体设为 null。
6. 是否错误地因为型号、寄存器名、引脚名、节点名、变量名或英文将保留原文而设为 null。
7. 是否遵守“出现任何语言文字即为非 null”的规则。
8. null 对应字体是否确实只承载通用数字、数学符号、运算符、图形符号、图标、Dingbats 或特殊字形。
9. 每个非 null 值是否只包含 `target_font_file` 和 `download_url`。
10. `target_font_file` 是否仅包含文件名而不包含目录。
11. 字体文件扩展名是否严格为 `.otf` 或 `.ttf`。
12. 每个非 null 目标字体是否都有对应的 `curl.exe` 下载命令。
13. JSON 中的 `download_url` 是否与对应 curl 命令中的 URL 完全一致。
14. 返回 null 的字体是否没有对应下载命令。
15. 三个规定区块之外是否完全没有其他内容。
16. 是否已亲自下载并打开全部相关单页 PDF。
17. 是否使用 `{pymupdf_version}` 完成测试。
18. 是否使用 fontTools 扫描了每个目标字体的全部 Unicode cmap。
19. 是否把全部标准/兼容字形歧义涉及的标准汉字加入了往返测试。
20. 是否分别完成了 `insert_text()` 和 `insert_textbox()` 测试。
21. 输入和提取结果是否未经归一化就逐码位完全相同。
22. 校验报告是否覆盖最终映射引用的每一个不同字体文件，且没有多余字体。
23. 映射中是否引用了 `result` 不为 `pass` 的字体。
24. 映射、下载命令和校验报告中的文件名、URL 是否完全一致。
25. 校验报告中的 SHA256 和文件大小是否来自实际完整 Base64 解码后的本地字体文件。
26. 当前环境没有真实校验能力或字体获取工具发生系统性不可用时，是否正确输出了 `[本地无校验工具]`，而不是猜测通过。
27. 无法下载或打开任意相关 PDF 时，是否正确输出了 `[无法下载PDF]`。
28. 是否错误地再次返回了“禁止重复使用的失败字体”中的相同文件名、URL、SHA256 或同一文件的镜像。
29. 每一个非 null 目标字体是否确实来自 `google/fonts` `main` 分支。
30. 每一个非 null 目标字体是否确实为 `.ttf` 或 `.otf`，而不是 Bridge 同样能够浏览到的 `.ttc`、`.woff`、`.woff2` 或其他格式。
31. 每一个不同目标字体是否都通过固定 Google Fonts Bridge 的实际 HTML 链接完成了字体选择、Action 和结果获取流程，而不是自行猜测内部 URL。
32. 每一个不同目标字体是否都实际取得了 `GET_METADATA` 和完整 `GET_BASE64` 内容。
33. 是否实际解析并验证了 `GET_METADATA` JSON，而不是仅因为 HTTP 200 就认定成功。
34. `GET_METADATA` 是否至少真实包含 `source_url`、`final_url`、`filename`、`size_bytes`、`sha256` 和 `detected_format`。
35. 如果网页读取无法直接展示完整 `GET_BASE64`，是否改用页面实际提供的 `GET_BASE64` URL 将完整响应保存到了本地 Base64 文本文件，而不是使用截断内容或立即判定工具不可用。
36. 如果使用 URL→本地文件保存 Base64，所使用的 URL 是否确实来自页面实际提供的 `GET_BASE64` 链接，而不是自行构造。
37. 是否确认保存得到的 GET_BASE64 响应实际是纯 Base64，而不是 HTTP 200 的 HTML 错误页、状态页、JSON 错误内容或其他无效正文。
38. 是否错误地使用 `source_url`、`final_url`、GitHub raw URL、CDN URL 或其他字体二进制直链直接下载了本地验证字体，从而绕过规定的 Base64 获取流程。
39. 是否真正使用 Python 读取完整 Base64，并把它解码为了本地字体文件。
40. Base64 解码前是否只忽略了标准 ASCII whitespace，而没有修改任何其他 Base64 字符。
41. 是否使用严格 Base64 解码，而没有尝试修补、补写或猜测截断 Base64。
42. 如果 Base64 通过本地文本文件落盘，Python 是否直接读取完整文件，而没有先把全文输出到可能截断的模型上下文或终端中转。
43. Base64 解码后的文件大小是否与 metadata `size_bytes` 完全一致。
44. Base64 解码后的本地 SHA256 是否与 metadata `sha256` 完全一致。
45. `target_font_file` 是否与 metadata `filename` 完全一致。
46. 最终映射、校验报告和 curl 命令中的 `download_url` 是否都与 metadata `source_url` 完全一致。
47. 是否错误地把 `GET_BASE64`、`GET_METADATA`、`/font/`、`/encode/`、`/locate/`、`/status/` 或 `/result/` Bridge URL 写入了最终 `download_url`。
48. 是否把 Base64 文本本身写进了最终 JSON 或下载命令。
49. 是否把用于保存 Base64 的临时 `.txt`、`.b64` 文件路径写进了最终 JSON、校验报告或下载命令。
50. 是否使用成功解码并验证的真实字体文件实际生成了视觉测试内容。
51. 是否实际查看了生成的字体渲染结果，而不是只运行渲染代码。
52. 是否结合代表 PDF 中对应映射键的实际文字、字号、bbox 和页面用途进行了视觉比较。
53. 是否比较了笔画重量、视觉黑度、字面宽度、紧凑程度、衬线/无衬线、等宽感、粗体/斜体/窄体特征以及中英混排协调性。
54. 是否因为某个候选技术上通过就忽略了明显的视觉不匹配。
55. 是否错误依赖生产阶段无法明确控制的 Variable Font 可变轴来声称视觉匹配。
56. 如果单个候选获取或校验失败，是否先继续寻找了其他候选，而不是错误使用特殊出口。
57. 如果使用 `[本地无校验工具]`，是否确实属于本地校验能力或字体获取工具的系统性不可用，而不是普通候选失败。
58. 是否错误地把“网页无法直接显示完整大型 Base64”本身当成了 `[本地无校验工具]` 的充分条件。
59. 如果网页无法直接显示完整大型 Base64，但当前工具支持把实际 `GET_BASE64` 响应完整保存到本地，是否确实完成了该落盘流程。
60. 是否把 Bridge SHA256 一致错误地当成完整字体校验，而遗漏了 fontTools、视觉分析或 PyMuPDF 精确往返测试。
61. 是否把网页搜索、Google Fonts 预览或字体介绍错误地当成真实字体视觉校验结果。
62. 当前模型用于 fontTools、视觉分析和 PyMuPDF 往返测试的实际字体文件，是否确实由规定 Bridge 流程取得的完整 Base64 解码产生。
63. 如果遇到 `queued`、`in_progress`、`PENDING` 或 `WAITING_FOR_WORKFLOW_RUN`，是否按照页面实际提供的状态链接继续处理，而没有伪造成功结果。
64. 如果遇到 `too_many_active_runs`，是否正确理解为本次 Action 尚未 dispatch，而没有错误刷新一个不存在的 run。
65. 如果遇到 `daily_limit_reached`，是否正确理解为本次 Action 尚未 dispatch，而没有自行编造 run ID 或 status URL。
66. 是否错误地把 Bridge 错误页面的 HTTP 200 当成字体获取、metadata 获取或 Base64 获取成功的充分证据。

"""

FONT_MAPPING_FOLLOWUP_PROMPT_TEMPLATE = FONT_MAPPING_PROMPT_TEMPLATE

FONT_DOWNLOAD_START = "[字体下载命令行 START]"
FONT_DOWNLOAD_END = "[字体下载命令行 END]"
FONT_VALIDATION_START = "[字体本地校验报告 START]"
FONT_VALIDATION_END = "[字体本地校验报告 END]"
FONT_MAPPING_START = "[字体映射表 START]"
FONT_MAPPING_END = "[字体映射表 END]"
PDF_DOWNLOAD_UNAVAILABLE_MARKER = "[无法下载PDF]"
LOCAL_VALIDATION_TOOL_UNAVAILABLE_MARKER = "[本地无校验工具]"
REJECTED_FONT_PROMPT_PLACEHOLDER = "{禁止重复使用的失败字体}"


# ============================================================
# 3. 数据模型
# ============================================================


@dataclass
class FontSample:
    page_num: int
    text: str
    size: float
    bbox: tuple[float, float, float, float]
    score: float


@dataclass
class FontRecord:
    key: str
    raw_names: set[str] = field(default_factory=set)
    pages: set[int] = field(default_factory=set)
    span_count: int = 0
    char_count: int = 0
    size_counter: Counter[float] = field(default_factory=Counter)
    flags_counter: Counter[int] = field(default_factory=Counter)
    samples: list[FontSample] = field(default_factory=list)
    resource_basefonts: set[str] = field(default_factory=set)
    resource_types: set[str] = field(default_factory=set)
    resource_exts: set[str] = field(default_factory=set)
    resource_encodings: set[str] = field(default_factory=set)

    def add_sample(self, sample: FontSample) -> None:
        normalized = normalize_sample_text(sample.text)
        if not normalized:
            return

        # 同一字体尽量保留不同文字内容。
        existing_texts = {normalize_sample_text(item.text) for item in self.samples}
        if normalized in existing_texts:
            return

        self.samples.append(sample)
        self.samples.sort(key=lambda item: item.score, reverse=True)
        del self.samples[MAX_SAMPLES_PER_FONT:]


@dataclass
class PageFontStat:
    chars: int = 0
    spans: int = 0
    max_size: float = 0.0


@dataclass
class ModelResponse:
    content_text: str
    reasoning_text: str
    finish_reason: str | None
    saw_done: bool
    is_sse: bool
    stream_error: str | None
    report_url: str | None
    elapsed_seconds: float
    first_data_seconds: float | None
    sse_line_count: int

    @property
    def merged_text(self) -> str:
        return self.reasoning_text + self.content_text

    def candidates(self) -> list[str]:
        values: list[str] = []
        for value in (self.content_text, self.merged_text, self.reasoning_text):
            if value and value not in values:
                values.append(value)
        return values


@dataclass
class AsyncReportResult:
    status: str
    task_id: str
    updated_at: str
    error_message: str
    content: str


@dataclass(frozen=True)
class FontMappingDecision:
    target_font_file: str
    download_url: str


@dataclass(frozen=True)
class RejectedFontCandidate:
    target_font_file: str
    download_url: str
    sha256: str
    reason: str
    rejected_at: str


@dataclass
class MappingRaceCopyResult:
    copy_id: str
    work_dir: Path
    font_dir: Path
    success: bool
    commands_text: str = ""
    decisions: dict[str, FontMappingDecision | None] = field(default_factory=dict)
    validation_report: dict[str, Any] = field(default_factory=dict)
    validated_raw: str = ""
    local_metadata: dict[str, dict[str, Any]] = field(default_factory=dict)
    rejected_candidate: RejectedFontCandidate | None = None
    error_message: str = ""


class RetriableModelMarker(RuntimeError):
    def __init__(self, marker: str):
        super().__init__(marker)
        self.marker = marker


class FontCandidateValidationError(RuntimeError):
    def __init__(
        self,
        target_font_file: str,
        download_url: str,
        reason: str,
        sha256: str = "",
    ) -> None:
        super().__init__(reason)
        self.target_font_file = target_font_file
        self.download_url = download_url
        self.sha256 = sha256.lower().strip()
        self.reason = reason


class RejectedFontReuseError(RuntimeError):
    pass


# ============================================================
# 4. 通用配置读取
# ============================================================


def read_literal_assignment(script_path: Path, variable_name: str, default: Any = None) -> Any:
    """从现有 Python 脚本读取简单字面量赋值，不导入、不执行该脚本。"""
    source = script_path.read_text(encoding="utf-8-sig")
    tree = ast.parse(source, filename=str(script_path))

    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id == variable_name:
                    try:
                        return ast.literal_eval(node.value)
                    except Exception:
                        return default
        elif isinstance(node, ast.AnnAssign):
            if isinstance(node.target, ast.Name) and node.target.id == variable_name:
                try:
                    return ast.literal_eval(node.value)
                except Exception:
                    return default

    return default


def resolve_runtime_config(args: argparse.Namespace) -> tuple[Path, Path, Path, Path]:
    script_dir = Path(__file__).resolve().parent
    transcribe_script = Path(args.transcribe_script).expanduser()
    if not transcribe_script.is_absolute():
        transcribe_script = (script_dir / transcribe_script).resolve()

    if not transcribe_script.is_file():
        raise FileNotFoundError(f"未找到转录脚本：{transcribe_script}")

    pdf_value = args.pdf or read_literal_assignment(transcribe_script, "PDF_INPUT")
    if not pdf_value:
        raise RuntimeError("无法从转录脚本读取 PDF_INPUT，请使用 --pdf 显式指定 PDF。")

    pdf_path = Path(str(pdf_value)).expanduser().resolve()
    if not pdf_path.is_file():
        raise FileNotFoundError(f"未找到 PDF：{pdf_path}")

    output_root = (
        Path(args.output_root).expanduser()
        if args.output_root
        else pdf_path.parent / OUTPUT_ROOT_NAME
    ).resolve()

    shared_dir = output_root / SHARED_RESOURCE_DIR_NAME
    work_dir = shared_dir / FONT_STAGE_WORK_DIR_NAME
    return transcribe_script, pdf_path, output_root, work_dir


def get_shared_dir(output_root: Path) -> Path:
    return output_root / SHARED_RESOURCE_DIR_NAME


def get_font_dir(output_root: Path) -> Path:
    return get_shared_dir(output_root) / FONT_DIR_RELATIVE


def get_mapping_path(output_root: Path) -> Path:
    return get_shared_dir(output_root) / FONT_MAPPING_FILE_NAME


def get_mapping_race_copy_dir(
    work_dir: Path,
    round_num: int,
    validation_cycle: int,
    copy_id: str,
) -> Path:
    """返回单个竞速副本唯一的工作目录，绝不与主目录或其他副本共享。"""
    safe_copy_id = re.sub(r"[^0-9A-Za-z_-]+", "_", copy_id).strip("_")
    if not safe_copy_id:
        raise ValueError(f"竞速副本 ID 无效：{copy_id!r}")
    return (
        work_dir
        / MAPPING_RACE_COPY_DIR_NAME
        / f"round_{round_num:03d}"
        / f"cycle_{validation_cycle:04d}"
        / safe_copy_id
    )


def get_mapping_race_font_dir(copy_work_dir: Path) -> Path:
    """竞速副本候选字体的专属目录；验证成功前不触碰公共 fonts 目录。"""
    return copy_work_dir / "resources" / "fonts"


def get_pymupdf_version() -> str:
    for attr_name in ("VersionBind", "pymupdf_version", "__version__"):
        value = getattr(fitz, attr_name, None)
        if value:
            return str(value).strip()
    version_tuple = getattr(fitz, "version", None)
    if isinstance(version_tuple, (tuple, list)) and version_tuple:
        return str(version_tuple[0]).strip()
    return "unknown"


def mapping_file_is_current(path: Path) -> bool:
    if not path.is_file() or path.stat().st_size <= 0:
        return False
    try:
        payload = json.loads(path.read_text(encoding="utf-8-sig"))
    except Exception:
        return False

    if not isinstance(payload, dict) or payload.get("version") != 3:
        return False
    if payload.get("font_validation_version") != FONT_VALIDATION_VERSION:
        return False

    mappings = payload.get("mappings")
    if not isinstance(mappings, dict) or not mappings:
        return False

    for entry in mappings.values():
        if entry is None:
            continue
        if not isinstance(entry, dict):
            return False
        if set(entry) != {
            "target_font_file",
            "download_url",
            "sha256",
            "size_bytes",
        }:
            return False
        if not isinstance(entry.get("target_font_file"), str) or not entry.get("target_font_file"):
            return False
        if not isinstance(entry.get("download_url"), str) or not entry.get("download_url"):
            return False
        if not isinstance(entry.get("sha256"), str) or not entry.get("sha256"):
            return False
        if not isinstance(entry.get("size_bytes"), int) or entry.get("size_bytes") <= 0:
            return False

    return True


# ============================================================
# 5. 字体名称、样例和属性辅助
# ============================================================


_SUBSET_PREFIX_RE = re.compile(r"(^|_)([A-Z]{6})\+")


def normalize_font_key(name: str) -> str:
    """
    生成阶段 4 查询时使用的映射键。

    PyMuPDF 的文本提取有时会返回 ABCDEF+FontName 形式的 PDF 子集前缀。
    这里移除此类六位大写前缀，但不主动合并 Arial_00、ArialMT 等其他名称，
    避免仅凭名称猜测把不同字体错误合并。
    """
    value = str(name or "").strip()
    value = value.lstrip("/")
    value = _SUBSET_PREFIX_RE.sub(r"\1", value)
    return value or "[UNKNOWN_FONT]"


def normalize_resource_basefont(name: str) -> str:
    value = str(name or "").strip().lstrip("/")
    return _SUBSET_PREFIX_RE.sub(r"\1", value)


def normalize_sample_text(text: str) -> str:
    value = re.sub(r"\s+", " ", str(text or "")).strip()
    return value


def clip_sample_text(text: str) -> str:
    value = normalize_sample_text(text)
    if len(value) > MAX_SAMPLE_TEXT_LENGTH:
        return value[: MAX_SAMPLE_TEXT_LENGTH - 1] + "…"
    return value


def count_visible_chars(text: str) -> int:
    return sum(1 for char in text if not char.isspace())


def sample_score(text: str, size: float) -> float:
    visible = count_visible_chars(text)
    alnum = sum(1 for char in text if char.isalnum())
    punctuation_penalty = max(0, visible - alnum) * 0.15
    return visible * max(1.0, min(float(size), 30.0)) + alnum * 2.0 - punctuation_penalty


def flags_description(flags: int, font_name: str) -> str:
    hints: list[str] = []
    lower_name = font_name.casefold()

    italic = bool(flags & getattr(fitz, "TEXT_FONT_ITALIC", 2)) or any(
        token in lower_name for token in ("italic", "oblique")
    )
    bold = bool(flags & getattr(fitz, "TEXT_FONT_BOLD", 16)) or any(
        token in lower_name for token in ("bold", "black", "heavy", "semibold", "demi")
    )
    mono = bool(flags & getattr(fitz, "TEXT_FONT_MONOSPACED", 8)) or any(
        token in lower_name for token in ("mono", "courier", "code")
    )
    serif = bool(flags & getattr(fitz, "TEXT_FONT_SERIFED", 4))
    narrow = any(token in lower_name for token in ("narrow", "condensed", "compressed"))

    hints.append("粗体" if bold else "常规粗细")
    if italic:
        hints.append("斜体/倾斜")
    if narrow:
        hints.append("窄体/压缩")
    if mono:
        hints.append("等宽")
    else:
        hints.append("衬线提示" if serif else "无衬线提示")

    return "、".join(hints) + "（PDF 字体标志可能不完全可靠）"


def format_number_list(values: Iterable[int], limit: int = MAX_LISTED_PAGES_PER_FONT) -> str:
    ordered = sorted(set(int(value) for value in values))
    if not ordered:
        return "（无）"
    if len(ordered) <= limit:
        return "、".join(str(value) for value in ordered)
    prefix = "、".join(str(value) for value in ordered[:limit])
    return f"{prefix}……（共 {len(ordered)} 页）"


# ============================================================
# 6. 整本 PDF 字体提取
# ============================================================


def extract_font_inventory(
    pdf_path: Path,
) -> tuple[dict[str, FontRecord], dict[int, dict[str, PageFontStat]]]:
    """只统计页面实际提取到的可见非空文字 span。"""
    font_records: dict[str, FontRecord] = {}
    page_stats: dict[int, dict[str, PageFontStat]] = defaultdict(dict)

    # 尽可能保留子集字体名，再由 normalize_font_key 明确去除子集前缀。
    try:
        fitz.TOOLS.set_subset_fontnames(True)
    except Exception:
        pass

    with fitz.open(str(pdf_path)) as doc:
        if doc.page_count <= 0:
            raise RuntimeError("PDF 没有页面")

        print(f"=== 提取整本 PDF 实际可见字体：共 {doc.page_count} 页 ===")

        for page_index in range(doc.page_count):
            page_num = page_index + 1
            page = doc.load_page(page_index)

            try:
                text_dict = page.get_text("dict", sort=False)
            except TypeError:
                text_dict = page.get_text("dict")

            for block in text_dict.get("blocks", []):
                if block.get("type") != 0:
                    continue
                for line in block.get("lines", []):
                    for span in line.get("spans", []):
                        text = str(span.get("text") or "")
                        if not text.strip():
                            continue

                        raw_name = str(span.get("font") or "[UNKNOWN_FONT]").strip()
                        key = normalize_font_key(raw_name)
                        size = round(float(span.get("size") or 0.0), 2)
                        flags = int(span.get("flags") or 0)
                        bbox_value = span.get("bbox") or (0.0, 0.0, 0.0, 0.0)
                        bbox = tuple(round(float(value), 2) for value in bbox_value)
                        visible_chars = count_visible_chars(text)
                        if visible_chars <= 0:
                            continue

                        record = font_records.setdefault(key, FontRecord(key=key))
                        record.raw_names.add(raw_name)
                        record.pages.add(page_num)
                        record.span_count += 1
                        record.char_count += visible_chars
                        record.size_counter[size] += 1
                        record.flags_counter[flags] += 1
                        record.add_sample(
                            FontSample(
                                page_num=page_num,
                                text=clip_sample_text(text),
                                size=size,
                                bbox=bbox,
                                score=sample_score(text, size),
                            )
                        )

                        stat = page_stats[page_num].setdefault(key, PageFontStat())
                        stat.chars += visible_chars
                        stat.spans += 1
                        stat.max_size = max(stat.max_size, size)

            # 页面字体资源仅用于补充信息；不据此新增“未实际显示”的字体。
            try:
                page_font_resources = doc.get_page_fonts(page_index, full=True)
            except Exception:
                page_font_resources = []

            for item in page_font_resources:
                if len(item) < 6:
                    continue
                xref, ext, font_type, basefont, _resource_name, encoding = item[:6]
                normalized_base = normalize_resource_basefont(str(basefont))

                matched_keys = [
                    key
                    for key in page_stats.get(page_num, {})
                    if key.casefold() == normalized_base.casefold()
                    or normalized_base.casefold().endswith(key.casefold())
                    or key.casefold().endswith(normalized_base.casefold())
                ]

                for key in matched_keys:
                    record = font_records[key]
                    record.resource_basefonts.add(str(basefont))
                    if font_type:
                        record.resource_types.add(str(font_type))
                    if ext:
                        record.resource_exts.add(str(ext))
                    if encoding:
                        record.resource_encodings.add(str(encoding))

            if page_num == 1 or page_num % 10 == 0 or page_num == doc.page_count:
                print(
                    f"  已扫描 {page_num}/{doc.page_count} 页；"
                    f"当前实际字体款式 {len(font_records)} 种"
                )

    if not font_records:
        raise RuntimeError("未从 PDF 提取到任何实际可见文字字体")

    print(f"✓ 字体提取完成：{len(font_records)} 种实际字体款式")
    return font_records, dict(page_stats)


# ============================================================
# 7. 选择尽量少的代表页面
# ============================================================


def page_quality_for_new_fonts(
    page_num: int,
    new_fonts: set[str],
    page_stats: dict[int, dict[str, PageFontStat]],
) -> float:
    quality = 0.0
    for font_key in new_fonts:
        stat = page_stats[page_num][font_key]
        # 字符多、字号大，更容易让模型辨认。
        quality += math.log1p(stat.chars) * (1.0 + min(stat.max_size, 24.0) / 24.0)
    return quality


def select_representative_pages(
    font_records: dict[str, FontRecord],
    page_stats: dict[int, dict[str, PageFontStat]],
) -> list[int]:
    """
    贪心集合覆盖：优先选能覆盖最多尚未覆盖字体的页面；
    覆盖数量相同时，优先选这些字体文字更多、字号更大的页面。
    """
    uncovered = set(font_records)
    selected: list[int] = []
    available_pages = set(page_stats)

    while uncovered:
        best_page: int | None = None
        best_new_fonts: set[str] = set()
        best_tuple: tuple[int, float, int, int] | None = None

        for page_num in sorted(available_pages - set(selected)):
            page_fonts = set(page_stats.get(page_num, {}))
            new_fonts = page_fonts & uncovered
            if not new_fonts:
                continue

            quality = page_quality_for_new_fonts(page_num, new_fonts, page_stats)
            total_chars = sum(page_stats[page_num][font].chars for font in new_fonts)
            # page_num 使用负数，使同分时优先较前页，结果更稳定。
            candidate_tuple = (len(new_fonts), quality, total_chars, -page_num)

            if best_tuple is None or candidate_tuple > best_tuple:
                best_tuple = candidate_tuple
                best_page = page_num
                best_new_fonts = new_fonts

        if best_page is None:
            missing = sorted(uncovered)
            raise RuntimeError(f"无法为以下字体找到代表页面：{missing}")

        selected.append(best_page)
        uncovered -= best_new_fonts
        print(
            f"  选择第 {best_page} 页，新增覆盖 {len(best_new_fonts)} 种字体："
            f"{', '.join(sorted(best_new_fonts))}"
        )

    selected.sort()
    print(f"✓ 使用 {len(selected)} 个代表页面覆盖全部 {len(font_records)} 种字体")
    return selected


def select_additional_evidence_pages(
    unresolved_keys: set[str],
    page_stats: dict[int, dict[str, PageFontStat]],
    already_selected: set[int],
) -> list[int]:
    """
    为每个未决字体在本轮尽量再提供一个尚未看过的代表页面。
    同一新页面可以同时覆盖多个未决字体。
    """
    unresolved_with_candidates = {
        key
        for key in unresolved_keys
        if any(
            page_num not in already_selected and key in page_fonts
            for page_num, page_fonts in page_stats.items()
        )
    }

    remaining = set(unresolved_with_candidates)
    selected_this_round: list[int] = []

    while remaining:
        best_page: int | None = None
        best_new_fonts: set[str] = set()
        best_tuple: tuple[int, float, int, int] | None = None

        for page_num in sorted(set(page_stats) - already_selected - set(selected_this_round)):
            page_fonts = set(page_stats.get(page_num, {}))
            new_fonts = page_fonts & remaining
            if not new_fonts:
                continue

            quality = page_quality_for_new_fonts(page_num, new_fonts, page_stats)
            total_chars = sum(page_stats[page_num][font].chars for font in new_fonts)
            candidate_tuple = (len(new_fonts), quality, total_chars, -page_num)

            if best_tuple is None or candidate_tuple > best_tuple:
                best_tuple = candidate_tuple
                best_page = page_num
                best_new_fonts = new_fonts

        if best_page is None:
            break

        selected_this_round.append(best_page)
        remaining -= best_new_fonts

    selected_this_round.sort()
    return selected_this_round


# ============================================================
# 8. 单页 PDF 拆分与 GitHub 上传
# ============================================================


def safe_pdf_stem(pdf_path: Path) -> str:
    safe = re.sub(r"[^a-zA-Z0-9]", "_", pdf_path.stem)
    safe = re.sub(r"_+", "_", safe).strip("_")
    if len(safe) > 40:
        safe = safe[:40]
    return safe or "pdf"


def get_github_folder_name(pdf_path: Path) -> str:
    # 与阶段 4.3 保持一致，后续上传全书单页时可直接复用同一目录。
    return safe_pdf_stem(pdf_path) + "_pdf_pages"


def parse_github_repo(repo_url: str) -> tuple[str, str]:
    normalized = repo_url.strip().rstrip("/")
    match = re.fullmatch(
        r"https://github\.com/([^/]+)/([^/]+?)(?:\.git)?",
        normalized,
        flags=re.IGNORECASE,
    )
    if not match:
        match = re.fullmatch(
            r"git@github\.com:([^/]+)/([^/]+?)(?:\.git)?",
            normalized,
            flags=re.IGNORECASE,
        )
    if not match:
        raise ValueError(f"无法解析 GitHub 仓库地址：{repo_url}")
    return match.group(1), match.group(2)


def build_raw_pdf_url(
    repo_url: str,
    branch: str,
    folder_name: str,
    page_num: int,
) -> str:
    owner, repo = parse_github_repo(repo_url)
    return (
        f"https://raw.githubusercontent.com/{quote(owner)}/{quote(repo)}/"
        f"{quote(branch, safe='')}/{quote(folder_name)}/{page_num}.pdf"
    )


def split_selected_pages(
    pdf_path: Path,
    pages_dir: Path,
    selected_pages: list[int],
    force: bool,
) -> None:
    pages_dir.mkdir(parents=True, exist_ok=True)

    with fitz.open(str(pdf_path)) as src_doc:
        for page_num in selected_pages:
            if page_num < 1 or page_num > src_doc.page_count:
                raise ValueError(f"代表页超出 PDF 范围：{page_num}")

            output_path = pages_dir / f"{page_num}.pdf"
            if output_path.is_file() and output_path.stat().st_size > 0 and not force:
                continue

            temp_path = output_path.with_name(output_path.name + ".tmp")
            temp_path.unlink(missing_ok=True)

            single_doc = fitz.open()
            try:
                single_doc.insert_pdf(
                    src_doc,
                    from_page=page_num - 1,
                    to_page=page_num - 1,
                )
                single_doc.save(str(temp_path), garbage=4, deflate=True)
            finally:
                single_doc.close()

            if not temp_path.is_file() or temp_path.stat().st_size <= 0:
                raise RuntimeError(f"拆分第 {page_num} 页失败")
            os.replace(temp_path, output_path)

    print(f"✓ 已准备 {len(selected_pages)} 个代表单页 PDF：{pages_dir}")


def run_git(args: list[str], cwd: Path | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    command = ["git"] + args
    print(f"  $ git {' '.join(args)}")
    result = subprocess.run(
        command,
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if result.stdout.strip():
        for line in result.stdout.strip().splitlines()[:8]:
            print(f"    {line}")
    if result.returncode != 0 and result.stderr.strip():
        for line in result.stderr.strip().splitlines()[:12]:
            print(f"    [stderr] {line}")
    if check and result.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} 失败，返回码 {result.returncode}\n{result.stderr[-2000:]}"
        )
    return result


def push_with_retry(args: list[str], cwd: Path, retries: int) -> None:
    for attempt in range(1, retries + 1):
        result = run_git(args, cwd=cwd, check=False)
        if result.returncode == 0:
            return
        if attempt < retries:
            print(f"  push 失败，5 秒后重试（{attempt}/{retries}）")
            time.sleep(5)
    raise RuntimeError(f"git push 在 {retries} 次尝试后仍然失败")


def upload_selected_pages_to_github(
    pages_dir: Path,
    selected_pages: list[int],
    folder_name: str,
    repo_url: str,
    branch: str,
    push_retry: int,
) -> None:
    files = [pages_dir / f"{page_num}.pdf" for page_num in selected_pages]
    missing = [str(path) for path in files if not path.is_file() or path.stat().st_size <= 0]
    if missing:
        raise FileNotFoundError(f"缺少待上传代表页：{missing}")

    temp_root = Path(
        tempfile.mkdtemp(
            prefix=f"_github_upload_temp_{folder_name}_font_mapping_",
            dir=str(pages_dir.parent),
        )
    )
    work_dir = temp_root / "repo"

    print("=== 上传字体代表单页 PDF 到 GitHub ===")
    print(f"仓库：{repo_url}")
    print(f"分支：{branch}")
    print(f"文件夹：{folder_name}")
    print(f"页面：{selected_pages}")
    print(f"临时目录：{work_dir}")

    try:
        clone_result = run_git(
            [
                "clone",
                "--depth",
                "1",
                "--filter=blob:none",
                "--no-checkout",
                repo_url,
                str(work_dir),
            ],
            check=False,
        )

        if clone_result.returncode != 0:
            raise RuntimeError(
                "克隆 GitHub 仓库失败，不允许在残留目录中执行 git init。\n"
                f"仓库：{repo_url}\n"
                f"临时目录：{work_dir}\n"
                f"stdout：\n{clone_result.stdout[-2000:]}\n"
                f"stderr：\n{clone_result.stderr[-2000:]}"
            )

        run_git(["sparse-checkout", "init", "--no-cone"], cwd=work_dir)
        run_git(
            ["sparse-checkout", "set", "README.md", folder_name],
            cwd=work_dir,
        )
        run_git(["checkout"], cwd=work_dir, check=False)

        run_git(["config", "http.version", "HTTP/1.1"], cwd=work_dir)
        run_git(["config", "core.compression", "0"], cwd=work_dir)
        run_git(["config", "http.postBuffer", "524288000"], cwd=work_dir)

        destination = work_dir / folder_name
        destination.mkdir(parents=True, exist_ok=True)
        for source in files:
            shutil.copy2(source, destination / source.name)

        for source in files:
            run_git(["add", str(Path(folder_name) / source.name)], cwd=work_dir)

        diff = run_git(["diff", "--cached", "--quiet"], cwd=work_dir, check=False)
        if diff.returncode == 0:
            print("✓ GitHub 上的代表页内容一致，无需提交")
            return
        if diff.returncode != 1:
            raise RuntimeError(f"检查 Git 暂存区失败，返回码 {diff.returncode}")

        page_label = "_".join(str(value) for value in selected_pages)
        run_git(["commit", "-m", f"upload font mapping pages {page_label}"], cwd=work_dir)
        push_with_retry(["push", "origin", branch], work_dir, push_retry)
        print("✓ 代表单页 PDF 上传完成")
    finally:
        cleanup_error: Exception | None = None

        for cleanup_attempt in range(1, 6):
            try:
                if temp_root.exists():
                    shutil.rmtree(temp_root)
                cleanup_error = None
                break
            except Exception as exc:
                cleanup_error = exc
                if cleanup_attempt < 5:
                    time.sleep(1)

        if cleanup_error is not None:
            print(
                "⚠ Git 临时目录清理失败，但不会复用该目录："
                f"{temp_root}\n"
                f"错误：{type(cleanup_error).__name__}: {cleanup_error}"
            )


# ============================================================
# 9. 生成库存文件和提示词
# ============================================================


def top_sizes(record: FontRecord) -> str:
    if not record.size_counter:
        return "未知"
    pairs = record.size_counter.most_common(6)
    return "、".join(f"{size:g} pt（{count} 个 span）" for size, count in pairs)


def dominant_flags(record: FontRecord) -> int:
    if not record.flags_counter:
        return 0
    return record.flags_counter.most_common(1)[0][0]


def build_font_table(
    font_records: dict[str, FontRecord],
    only_keys: set[str] | None = None,
) -> str:
    parts: list[str] = []
    keys = set(font_records) if only_keys is None else set(only_keys)

    for index, key in enumerate(
        sorted(keys, key=lambda value: value.casefold()),
        start=1,
    ):
        record = font_records[key]
        parts.append(f"#### FONT_{index:03d}")
        parts.append(f"- 映射键：{record.key}")
        parts.append(f"- 文本提取中出现的原始名称：{', '.join(sorted(record.raw_names))}")
        parts.append(f"- 款式提示：{flags_description(dominant_flags(record), record.key)}")
        parts.append(f"- 出现页数：{len(record.pages)} 页")
        parts.append(f"- 出现页面：{format_number_list(record.pages)}")
        parts.append(f"- 可见字符数：{record.char_count}")
        parts.append(f"- 文字 span 数：{record.span_count}")
        parts.append(f"- 常见字号：{top_sizes(record)}")

        if record.resource_basefonts:
            parts.append(f"- PDF 资源字体名：{', '.join(sorted(record.resource_basefonts))}")
        if record.resource_types:
            parts.append(f"- PDF 字体类型：{', '.join(sorted(record.resource_types))}")
        if record.resource_encodings:
            parts.append(f"- 编码：{', '.join(sorted(record.resource_encodings))}")

        if record.samples:
            parts.append("- 实际原文样例：")
            for sample in record.samples:
                bbox_text = ", ".join(f"{value:g}" for value in sample.bbox)
                parts.append(
                    f"  - 第 {sample.page_num} 页，{sample.size:g} pt，"
                    f"bbox=[{bbox_text}]：{sample.text}"
                )
        else:
            parts.append("- 实际原文样例：（未提取到）")

        parts.append("")

    return "\n".join(parts).rstrip()


def build_representative_page_list(
    selected_pages: list[int],
    page_stats: dict[int, dict[str, PageFontStat]],
    repo_url: str,
    branch: str,
    folder_name: str,
    only_fonts: set[str] | None = None,
) -> str:
    parts: list[str] = []
    for page_num in selected_pages:
        page_fonts = set(page_stats[page_num])
        if only_fonts is not None:
            page_fonts &= only_fonts
        fonts = sorted(page_fonts, key=lambda value: value.casefold())
        if not fonts:
            continue
        url = build_raw_pdf_url(repo_url, branch, folder_name, page_num)
        parts.append(
            f"#### 这是第 {page_num} 页的链接，它拥有"
            f"{', '.join(fonts)}，你需要判断这些字体应映射到中文字体还是返回 null"
        )
        parts.append("```")
        parts.append(url)
        parts.append("```")
        parts.append("")
    return "\n".join(parts).rstrip()


def get_rejected_font_candidates_path(work_dir: Path) -> Path:
    return work_dir / REJECTED_FONT_CANDIDATES_FILE_NAME


def load_rejected_font_candidates(work_dir: Path) -> list[RejectedFontCandidate]:
    path = get_rejected_font_candidates_path(work_dir)
    if not path.is_file() or path.stat().st_size <= 0:
        return []
    try:
        payload = json.loads(path.read_text(encoding="utf-8-sig"))
    except Exception as exc:
        print(
            f"  ⚠ 无法读取失败字体黑名单，将保留原文件并按空列表继续："
            f"{type(exc).__name__}: {exc}"
        )
        return []
    values = payload.get("rejected_fonts") if isinstance(payload, dict) else None
    if not isinstance(values, list):
        return []
    result: list[RejectedFontCandidate] = []
    for value in values:
        if not isinstance(value, dict):
            continue
        target_font_file = str(value.get("target_font_file") or "").strip()
        download_url = str(value.get("download_url") or "").strip()
        sha256 = str(value.get("sha256") or "").strip().lower()
        reason = str(value.get("reason") or "").strip()
        rejected_at = str(value.get("rejected_at") or "").strip()
        if not target_font_file and not download_url and not sha256:
            continue
        result.append(
            RejectedFontCandidate(
                target_font_file=target_font_file,
                download_url=download_url,
                sha256=sha256,
                reason=reason,
                rejected_at=rejected_at,
            )
        )
    return result


def save_rejected_font_candidates(
    work_dir: Path,
    candidates: list[RejectedFontCandidate],
) -> None:
    work_dir.mkdir(parents=True, exist_ok=True)
    path = get_rejected_font_candidates_path(work_dir)
    payload = {
        "version": 1,
        "pymupdf_version": get_pymupdf_version(),
        "rejected_fonts": [
            {
                "target_font_file": item.target_font_file,
                "download_url": item.download_url,
                "sha256": item.sha256,
                "reason": item.reason,
                "rejected_at": item.rejected_at,
            }
            for item in candidates
        ],
    }
    temp_path = path.with_name(path.name + ".tmp")
    temp_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    os.replace(temp_path, path)


def record_rejected_font_candidate(
    work_dir: Path,
    target_font_file: str,
    download_url: str,
    sha256: str,
    reason: str,
) -> RejectedFontCandidate:
    candidates = load_rejected_font_candidates(work_dir)
    normalized_filename = target_font_file.casefold().strip()
    normalized_url = download_url.strip()
    normalized_sha256 = sha256.lower().strip()
    for existing in candidates:
        same_filename = bool(
            normalized_filename
            and existing.target_font_file.casefold().strip() == normalized_filename
        )
        same_url = bool(normalized_url and existing.download_url == normalized_url)
        same_sha = bool(normalized_sha256 and existing.sha256 == normalized_sha256)
        if same_filename or same_url or same_sha:
            merged_reason = existing.reason
            if reason and reason not in merged_reason:
                merged_reason = (merged_reason + "；" + reason).strip("；")
            updated = RejectedFontCandidate(
                target_font_file=existing.target_font_file or target_font_file,
                download_url=existing.download_url or download_url,
                sha256=existing.sha256 or normalized_sha256,
                reason=merged_reason,
                rejected_at=existing.rejected_at or time.strftime("%Y-%m-%d %H:%M:%S"),
            )
            candidates[candidates.index(existing)] = updated
            save_rejected_font_candidates(work_dir, candidates)
            return updated

    candidate = RejectedFontCandidate(
        target_font_file=target_font_file.strip(),
        download_url=download_url.strip(),
        sha256=normalized_sha256,
        reason=reason.strip(),
        rejected_at=time.strftime("%Y-%m-%d %H:%M:%S"),
    )
    candidates.append(candidate)
    save_rejected_font_candidates(work_dir, candidates)
    return candidate


def build_rejected_font_prompt_text(
    candidates: list[RejectedFontCandidate],
) -> str:
    if not candidates:
        return "（当前没有已知失败字体。）"
    parts: list[str] = []
    for index, item in enumerate(candidates, start=1):
        parts.append(f"#### FAILED_FONT_{index:03d}")
        parts.append(f"- target_font_file：{item.target_font_file or '未知'}")
        parts.append(f"- download_url：{item.download_url or '未知'}")
        parts.append(f"- SHA256：{item.sha256 or '未知'}")
        parts.append(f"- 失败原因：{item.reason or '当前生产环境验证失败'}")
        parts.append(f"- 记录时间：{item.rejected_at or '未知'}")
        parts.append("")
    return "\n".join(parts).rstrip()


def render_prompt_with_rejected_fonts(
    prompt_template: str,
    candidates: list[RejectedFontCandidate],
) -> str:
    return prompt_template.replace(
        REJECTED_FONT_PROMPT_PLACEHOLDER,
        build_rejected_font_prompt_text(candidates),
    )


def build_prompt(
    font_records: dict[str, FontRecord],
    selected_pages: list[int],
    page_stats: dict[int, dict[str, PageFontStat]],
    repo_url: str,
    branch: str,
    folder_name: str,
) -> str:
    return (
        FONT_MAPPING_PROMPT_TEMPLATE
        .replace("{字体清单}", build_font_table(font_records))
        .replace(
            "{代表页面清单}",
            build_representative_page_list(
                selected_pages,
                page_stats,
                repo_url,
                branch,
                folder_name,
            ),
        )
        .replace("{pymupdf_version}", get_pymupdf_version())
    )


def build_followup_prompt(
    round_num: int,
    unresolved_keys: set[str],
    all_selected_pages: list[int],
    font_records: dict[str, FontRecord],
    page_stats: dict[int, dict[str, PageFontStat]],
    repo_url: str,
    branch: str,
    folder_name: str,
) -> str:
    return (
        FONT_MAPPING_FOLLOWUP_PROMPT_TEMPLATE
        .replace("{轮次}", str(round_num))
        .replace("{字体清单}", build_font_table(font_records, unresolved_keys))
        .replace(
            "{代表页面清单}",
            build_representative_page_list(
                all_selected_pages,
                page_stats,
                repo_url,
                branch,
                folder_name,
                only_fonts=unresolved_keys,
            ),
        )
        .replace("{pymupdf_version}", get_pymupdf_version())
    )


def write_selected_pages_file(work_dir: Path, selected_pages: list[int]) -> None:
    (work_dir / "00_selected_pages.json").write_text(
        json.dumps({"selected_pages": sorted(set(selected_pages))}, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def write_inventory_files(
    work_dir: Path,
    pdf_path: Path,
    font_records: dict[str, FontRecord],
    page_stats: dict[int, dict[str, PageFontStat]],
    selected_pages: list[int],
    prompt: str,
) -> None:
    work_dir.mkdir(parents=True, exist_ok=True)

    inventory = {
        "version": 1,
        "source_pdf": str(pdf_path),
        "source_pdf_sha256": sha256_file(pdf_path),
        "font_count": len(font_records),
        "fonts": [],
    }

    for key in sorted(font_records, key=lambda value: value.casefold()):
        record = font_records[key]
        inventory["fonts"].append(
            {
                "mapping_key": key,
                "raw_names": sorted(record.raw_names),
                "pages": sorted(record.pages),
                "span_count": record.span_count,
                "char_count": record.char_count,
                "common_sizes": [
                    {"size": size, "span_count": count}
                    for size, count in record.size_counter.most_common()
                ],
                "dominant_flags": dominant_flags(record),
                "style_hint": flags_description(dominant_flags(record), key),
                "samples": [
                    {
                        "page_num": item.page_num,
                        "text": item.text,
                        "size": item.size,
                        "bbox": list(item.bbox),
                    }
                    for item in record.samples
                ],
                "resource_basefonts": sorted(record.resource_basefonts),
                "resource_types": sorted(record.resource_types),
                "resource_exts": sorted(record.resource_exts),
                "resource_encodings": sorted(record.resource_encodings),
            }
        )

    page_payload = {
        str(page_num): {
            font_key: {
                "chars": stat.chars,
                "spans": stat.spans,
                "max_size": stat.max_size,
            }
            for font_key, stat in sorted(page_data.items())
        }
        for page_num, page_data in sorted(page_stats.items())
    }

    (work_dir / "00_font_inventory.json").write_text(
        json.dumps(inventory, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    (work_dir / "00_page_font_coverage.json").write_text(
        json.dumps(page_payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    write_selected_pages_file(work_dir, selected_pages)
    rendered_prompt = render_prompt_with_rejected_fonts(
        prompt,
        load_rejected_font_candidates(work_dir),
    )
    (work_dir / "00_font_mapping_prompt.txt").write_text(
        rendered_prompt,
        encoding="utf-8",
    )


# ============================================================
# 10. API Key、限速、异步报告和响应读取
# ============================================================


class KeyManager:
    def __init__(self, keys: list[str], max_fails: int):
        self._keys = list(keys)
        self._max_fails = max_fails
        self._current_index = 0
        self._fail_count = 0
        self._total_rotations = 0
        self._lock = threading.Lock()

    def get_current_key(self) -> str | None:
        with self._lock:
            if not self._keys:
                return None
            return self._keys[self._current_index]

    def get_current_info(self) -> tuple[int, int, int]:
        with self._lock:
            return self._current_index + 1, len(self._keys), self._fail_count

    def report_failure(self) -> None:
        with self._lock:
            if not self._keys:
                return
            self._fail_count += 1
            print(
                f"  ⚠ Key #{self._current_index + 1} "
                f"失败计数：{self._fail_count}/{self._max_fails}"
            )
            if self._fail_count >= self._max_fails:
                old_index = self._current_index
                self._current_index = (self._current_index + 1) % len(self._keys)
                self._fail_count = 0
                self._total_rotations += 1
                print(
                    f"  ⚠ Key #{old_index + 1} 连续失败，"
                    f"切换到 Key #{self._current_index + 1}；"
                    f"累计轮换 {self._total_rotations} 次"
                )

    def report_success(self) -> None:
        with self._lock:
            self._fail_count = 0


key_manager = KeyManager(API_KEYS, KEY_MAX_FAILS)
_request_lock = threading.Lock()
_last_request_time = 0.0


ASYNC_REPORT_URL_RE = re.compile(
    r"""https://async-report-cf-pages\.(?:toapis\.org|llm99\.com)/reports?/[^\s<>\]"'`)]+""",
    flags=re.IGNORECASE,
)



def wait_global_request_slot() -> None:
    global _last_request_time
    with _request_lock:
        now = time.time()
        wait_seconds = REQUEST_INTERVAL - (now - _last_request_time)
        if wait_seconds > 0:
            print(f"全局限速：等待 {wait_seconds:.1f} 秒……")
            time.sleep(wait_seconds)
        _last_request_time = time.time()


def build_session() -> requests.Session:
    session = requests.Session()
    session.trust_env = False
    if PROXY_URL:
        session.proxies = {"http": PROXY_URL, "https": PROXY_URL}
    return session


def response_content_to_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, (int, float, bool)):
        return str(value)
    if isinstance(value, list):
        return "".join(response_content_to_text(item) for item in value)
    if isinstance(value, dict):
        parts: list[str] = []
        for key in ("reasoning_content", "text", "content", "output_text"):
            if key in value:
                parts.append(response_content_to_text(value.get(key)))
        return "".join(parts)
    return ""


def extract_async_report_url(*values: Any) -> str | None:
    for value in values:
        if value is None:
            continue
        match = ASYNC_REPORT_URL_RE.search(str(value))
        if match:
            return match.group(0).rstrip(".,;:!?")
    return None


def format_local_timestamp(timestamp: float) -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(timestamp))


def get_async_report_state_path(work_dir: Path, round_num: int) -> Path:
    return work_dir / f"01_round_{round_num:03d}_async_report_state.json"


def get_async_report_url_path(work_dir: Path, round_num: int) -> Path:
    return work_dir / f"01_round_{round_num:03d}_async_report_url.txt"


def load_async_report_state(
    work_dir: Path,
    round_num: int,
    expected_prompt_sha256: str | None = None,
) -> dict[str, Any] | None:
    state_path = get_async_report_state_path(work_dir, round_num)

    if not state_path.is_file() or state_path.stat().st_size <= 0:
        return None

    try:
        data = json.loads(state_path.read_text(encoding="utf-8-sig"))
    except Exception as exc:
        print(
            f"  ⚠ 无法读取第 {round_num} 轮异步报告状态，将删除："
            f"{type(exc).__name__}: {exc}"
        )
        state_path.unlink(missing_ok=True)
        return None

    if not isinstance(data, dict):
        print(f"  ⚠ 第 {round_num} 轮异步报告状态格式错误，将删除")
        state_path.unlink(missing_ok=True)
        return None

    report_url = str(data.get("report_url") or "").strip()
    if not report_url or not ASYNC_REPORT_URL_RE.fullmatch(report_url):
        print(f"  ⚠ 第 {round_num} 轮异步报告状态中的 URL 无效，将删除")
        state_path.unlink(missing_ok=True)
        return None

    stored_prompt_sha256 = str(data.get("prompt_sha256") or "").strip().lower()
    if (
        expected_prompt_sha256
        and stored_prompt_sha256
        and stored_prompt_sha256 != expected_prompt_sha256.lower()
    ):
        print(
            f"  ⚠ 第 {round_num} 轮异步断点对应的提示词已变化，"
            "将清理旧断点并重新请求"
        )
        state_path.unlink(missing_ok=True)
        return None

    return data


def save_async_report_state(
    work_dir: Path,
    round_num: int,
    report_url: str,
    status: str,
    prompt_sha256: str,
    task_label: str,
    started_at_epoch: float | None = None,
    updated_at: str = "",
    error_message: str = "",
    completed_content_path: Path | None = None,
) -> dict[str, Any]:
    work_dir.mkdir(parents=True, exist_ok=True)

    existing = load_async_report_state(
        work_dir,
        round_num,
        expected_prompt_sha256=prompt_sha256,
    )
    now = time.time()

    if started_at_epoch is None:
        if existing and str(existing.get("report_url") or "").strip() == report_url:
            try:
                started_at_epoch = float(existing.get("started_at_epoch"))
            except (TypeError, ValueError):
                started_at_epoch = now
        else:
            started_at_epoch = now

    payload: dict[str, Any] = {
        "round_num": round_num,
        "task_label": task_label,
        "prompt_sha256": prompt_sha256,
        "report_url": report_url,
        "status": status,
        "started_at_epoch": started_at_epoch,
        "started_at_local": format_local_timestamp(started_at_epoch),
        "updated_at_epoch": now,
        "updated_at_local": format_local_timestamp(now),
        "report_updated_at": updated_at,
        "error_message": error_message,
        "timeout_seconds": float(ASYNC_REPORT_PROCESSING_TIMEOUT_SECONDS),
    }

    if completed_content_path is not None:
        payload["completed_content_path"] = str(completed_content_path.resolve())
    elif (
        existing
        and str(existing.get("report_url") or "").strip() == report_url
        and existing.get("completed_content_path")
    ):
        payload["completed_content_path"] = existing["completed_content_path"]

    state_path = get_async_report_state_path(work_dir, round_num)
    temp_path = state_path.with_name(state_path.name + ".tmp")
    temp_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    os.replace(temp_path, state_path)

    get_async_report_url_path(work_dir, round_num).write_text(
        report_url,
        encoding="utf-8",
    )

    return payload


def save_captured_async_report_url(
    work_dir: Path,
    round_num: int,
    report_url: str,
    prompt_sha256: str,
    task_label: str,
) -> dict[str, Any]:
    """首次捕获 URL 时立即落盘，固定异步报告总等待起点。"""
    existing = load_async_report_state(
        work_dir,
        round_num,
        expected_prompt_sha256=prompt_sha256,
    )

    if existing and str(existing.get("report_url") or "").strip() == report_url:
        return existing

    state = save_async_report_state(
        work_dir=work_dir,
        round_num=round_num,
        report_url=report_url,
        status="processing",
        prompt_sha256=prompt_sha256,
        task_label=task_label,
        started_at_epoch=time.time(),
    )

    print(
        f"  💾 已立即保存第 {round_num} 轮异步报告 URL："
        f"{get_async_report_url_path(work_dir, round_num)}"
    )
    return state


def clear_async_report_state(work_dir: Path, round_num: int) -> None:
    """删除活动状态；URL 文本保留，便于人工追踪。"""
    get_async_report_state_path(work_dir, round_num).unlink(missing_ok=True)


def get_async_report_remaining_seconds(started_at_epoch: float) -> float:
    elapsed = max(0.0, time.time() - started_at_epoch)
    return max(
        0.0,
        float(ASYNC_REPORT_PROCESSING_TIMEOUT_SECONDS) - elapsed,
    )


class _ResultContentHTMLParser(HTMLParser):
    _BLOCK_TAGS = {
        "address", "article", "aside", "blockquote", "div", "dl",
        "fieldset", "figcaption", "figure", "footer", "form",
        "h1", "h2", "h3", "h4", "h5", "h6", "header", "hr", "li",
        "main", "nav", "ol", "p", "pre", "section", "table", "tbody",
        "td", "tfoot", "th", "thead", "tr", "ul",
    }
    _VOID_TAGS = {
        "area", "base", "br", "col", "embed", "hr", "img", "input",
        "link", "meta", "param", "source", "track", "wbr",
    }

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self._depth = 0
        self._parts: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attrs_map = dict(attrs)
        if self._depth == 0:
            if attrs_map.get("id") == "resultContent":
                self._depth = 1
            return
        if tag in self._BLOCK_TAGS or tag == "br":
            self._parts.append("\n")
        if tag not in self._VOID_TAGS:
            self._depth += 1

    def handle_endtag(self, tag: str) -> None:
        if self._depth <= 0:
            return
        if tag in self._BLOCK_TAGS:
            self._parts.append("\n")
        self._depth -= 1

    def handle_data(self, data: str) -> None:
        if self._depth > 0:
            self._parts.append(data)

    def get_text(self) -> str:
        text = "".join(self._parts)
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        text = re.sub(r"[ \t]+\n", "\n", text)
        text = re.sub(r"\n{3,}", "\n\n", text)
        return text.strip()


def extract_async_report_initial_state(html_text: str) -> dict[str, Any]:
    match = re.search(r"window\.__INITIAL_STATE__\s*=\s*", html_text)
    if not match:
        return {}
    payload = html_text[match.end():].lstrip()
    try:
        state, _ = json.JSONDecoder().raw_decode(payload)
    except json.JSONDecodeError:
        return {}
    return state if isinstance(state, dict) else {}


def extract_async_report_dom_content(html_text: str) -> str:
    parser = _ResultContentHTMLParser()
    parser.feed(html_text)
    parser.close()
    return parser.get_text()


def fetch_async_report(session: requests.Session, report_url: str) -> AsyncReportResult:
    response = session.get(
        report_url,
        headers={
            "User-Agent": "Mozilla/5.0",
            "Cache-Control": "no-cache",
            "Pragma": "no-cache",
        },
        timeout=max(0.1, float(ASYNC_REPORT_REQUEST_TIMEOUT_SECONDS)),
    )
    response.raise_for_status()
    response.encoding = "utf-8"
    html_text = response.text
    state = extract_async_report_initial_state(html_text)
    content = response_content_to_text(state.get("content")).strip()
    if not content:
        content = extract_async_report_dom_content(html_text)
    status = response_content_to_text(state.get("status") or "unknown").strip().lower()
    task_id = response_content_to_text(
        state.get("taskId") or state.get("task_id") or "unknown"
    ).strip()
    updated_at = response_content_to_text(
        state.get("updated_at") or state.get("updatedAt")
    ).strip()
    error_message = response_content_to_text(
        state.get("error_message") or state.get("errorMessage")
    ).strip()
    return AsyncReportResult(
        status=status or "unknown",
        task_id=task_id or "unknown",
        updated_at=updated_at,
        error_message=error_message,
        content=content,
    )


def wait_for_async_report(
    report_url: str,
    work_dir: Path,
    round_num: int,
    prompt_sha256: str,
    task_label: str,
    started_at_epoch: float | None = None,
) -> AsyncReportResult:
    if started_at_epoch is None:
        started_at_epoch = time.time()

    timeout_seconds = max(0.1, float(ASYNC_REPORT_PROCESSING_TIMEOUT_SECONDS))
    poll_interval = max(0.1, float(ASYNC_REPORT_POLL_INTERVAL_SECONDS))
    remaining_at_start = get_async_report_remaining_seconds(started_at_epoch)

    print(
        f"  🌐 开始检查第 {round_num} 轮异步报告页：{report_url}\n"
        f"  ⏳ 首次记录：{format_local_timestamp(started_at_epoch)}；"
        f"剩余等待：{remaining_at_start:.1f} 秒"
    )

    save_async_report_state(
        work_dir=work_dir,
        round_num=round_num,
        report_url=report_url,
        status="processing",
        prompt_sha256=prompt_sha256,
        task_label=task_label,
        started_at_epoch=started_at_epoch,
    )

    attempt = 0
    last_snapshot: tuple[str, str, int, str] | None = None
    last_fetch_error = ""
    last_progress_print = 0.0

    with build_session() as session:
        while True:
            remaining = get_async_report_remaining_seconds(started_at_epoch)
            elapsed = max(0.0, time.time() - started_at_epoch)

            if remaining <= 0:
                timeout_message = (
                    f"异步报告页从首次记录时间开始计算，"
                    f"在 {timeout_seconds:g} 秒内未进入 completed/error 状态"
                )
                save_async_report_state(
                    work_dir=work_dir,
                    round_num=round_num,
                    report_url=report_url,
                    status="timeout",
                    prompt_sha256=prompt_sha256,
                    task_label=task_label,
                    started_at_epoch=started_at_epoch,
                    error_message=timeout_message,
                )
                return AsyncReportResult(
                    status="timeout",
                    task_id="unknown",
                    updated_at="",
                    error_message=timeout_message,
                    content="",
                )

            attempt += 1
            try:
                data = fetch_async_report(session, report_url)
                last_fetch_error = ""
            except Exception as exc:
                error_text = f"{type(exc).__name__}: {exc}"
                save_async_report_state(
                    work_dir=work_dir,
                    round_num=round_num,
                    report_url=report_url,
                    status="processing",
                    prompt_sha256=prompt_sha256,
                    task_label=task_label,
                    started_at_epoch=started_at_epoch,
                    error_message=error_text,
                )
                if error_text != last_fetch_error:
                    print(f"  ⚠ 报告页请求失败（第 {attempt} 次）：{error_text}")
                    last_fetch_error = error_text
                now = time.time()
                if now - last_progress_print >= ASYNC_REPORT_PROGRESS_PRINT_INTERVAL_SECONDS:
                    print(
                        f"  📡 异步报告仍在等待：总耗时 {elapsed:.1f} 秒；"
                        f"剩余 {remaining:.1f} 秒；最近请求错误：{error_text}"
                    )
                    last_progress_print = now
                time.sleep(min(poll_interval, remaining))
                continue

            save_async_report_state(
                work_dir=work_dir,
                round_num=round_num,
                report_url=report_url,
                status=data.status,
                prompt_sha256=prompt_sha256,
                task_label=task_label,
                started_at_epoch=started_at_epoch,
                updated_at=data.updated_at,
                error_message=data.error_message,
            )

            snapshot = (
                data.status,
                data.updated_at,
                len(data.content),
                data.error_message,
            )
            now = time.time()
            if (
                snapshot != last_snapshot
                or now - last_progress_print >= ASYNC_REPORT_PROGRESS_PRINT_INTERVAL_SECONDS
            ):
                print(
                    f"  📡 报告页状态：{data.status}；"
                    f"更新：{data.updated_at or '未知'}；"
                    f"内容：{len(data.content)} 字；"
                    f"总耗时：{elapsed:.1f} 秒；"
                    f"剩余：{remaining:.1f} 秒"
                )
                last_snapshot = snapshot
                last_progress_print = now

            if data.status == "completed":
                completed_path = (
                    work_dir
                    / f"01_round_{round_num:03d}_async_report_completed.raw.txt"
                )
                completed_path.write_text(data.content, encoding="utf-8")
                save_async_report_state(
                    work_dir=work_dir,
                    round_num=round_num,
                    report_url=report_url,
                    status="completed",
                    prompt_sha256=prompt_sha256,
                    task_label=task_label,
                    started_at_epoch=started_at_epoch,
                    updated_at=data.updated_at,
                    error_message=data.error_message,
                    completed_content_path=completed_path,
                )
                print(f"  ✓ 异步报告已完成，完整内容已保存：{completed_path}")
                return data

            if data.status in {"error", "failed", "cancelled"}:
                return data

            time.sleep(min(poll_interval, remaining))


def _print_stream_progress(
    task_label: str,
    elapsed: float,
    since_last_data: float,
    first_data_seconds: float | None,
    sse_line_count: int,
    reasoning_chars: int,
    content_chars: int,
    report_url: str | None,
) -> None:
    first_data_text = (
        f"{first_data_seconds:.1f} 秒"
        if first_data_seconds is not None
        else "尚未收到"
    )
    print(
        f"  📡 {task_label}仍在进行："
        f"总耗时 {elapsed:.1f} 秒；"
        f"距最近数据 {since_last_data:.1f} 秒；"
        f"首个数据 {first_data_text}；"
        f"SSE 行 {sse_line_count}；"
        f"推理 {reasoning_chars} 字；"
        f"正式输出 {content_chars} 字；"
        f"异步报告 {'已捕获' if report_url else '未捕获'}"
    )


def read_model_response(
    resp: requests.Response,
    task_label: str,
    work_dir: Path,
    round_num: int,
    prompt_sha256: str,
) -> ModelResponse:
    """
    在后台线程读取 requests 流，主线程每秒轮询并定期打印活动信息。
    这样即使模型长时间只输出 reasoning_content，控制台也不会看起来卡死。
    """
    resp.encoding = "utf-8"

    event_queue: queue.Queue[tuple[str, Any]] = queue.Queue()
    stop_event = threading.Event()

    def reader_worker() -> None:
        try:
            for raw_line in resp.iter_lines(chunk_size=1, decode_unicode=True):
                if stop_event.is_set():
                    break
                event_queue.put(("line", raw_line))
        except Exception as exc:
            event_queue.put(("error", exc))
        finally:
            event_queue.put(("eof", None))

    reader_thread = threading.Thread(
        target=reader_worker,
        name=f"font-mapping-stream-round-{round_num}",
        daemon=True,
    )
    reader_thread.start()

    content_parts: list[str] = []
    reasoning_parts: list[str] = []
    raw_lines: list[str] = []
    finish_reason: str | None = None
    saw_done = False
    is_sse = False
    stream_error: str | None = None
    report_url: str | None = None
    sse_line_count = 0

    start_time = time.time()
    first_data_time: float | None = None
    last_data_time = start_time
    last_progress_print = start_time
    printed_reasoning_started = False
    printed_content_started = False

    def capture_report_url(*values: Any) -> None:
        nonlocal report_url
        if report_url is not None:
            return
        candidate = extract_async_report_url(*values)
        if not candidate:
            return
        report_url = candidate
        save_captured_async_report_url(
            work_dir=work_dir,
            round_num=round_num,
            report_url=candidate,
            prompt_sha256=prompt_sha256,
            task_label=task_label,
        )
        print(f"  🔗 已捕获异步报告页：{candidate}")

    def append_reasoning(piece: str) -> None:
        nonlocal printed_reasoning_started
        if not piece:
            return
        reasoning_parts.append(piece)
        if not printed_reasoning_started:
            print(
                f"  🧠 已开始收到 reasoning_content；"
                "为避免刷屏，仅显示累计字符数，不打印完整推理文本"
            )
            printed_reasoning_started = True
        if DEBUG_PRINT_REASONING_CONTENT:
            print(piece, end="", flush=True)

    def append_content(piece: str) -> None:
        nonlocal printed_content_started
        if not piece:
            return
        content_parts.append(piece)
        if not printed_content_started:
            print("  ✍ 已开始收到正式 content 输出：")
            printed_content_started = True
        if DEBUG_PRINT_STREAM:
            print(piece, end="", flush=True)

    while True:
        now = time.time()
        elapsed = now - start_time
        since_last_data = now - last_data_time

        timeout_reason: str | None = None
        if first_data_time is None and elapsed > STREAM_FIRST_DATA_TIMEOUT_SECONDS:
            timeout_reason = (
                f"首个流数据等待超过 {STREAM_FIRST_DATA_TIMEOUT_SECONDS:g} 秒"
            )
        elif first_data_time is not None and since_last_data > STREAM_IDLE_TIMEOUT_SECONDS:
            timeout_reason = (
                f"流数据空闲超过 {STREAM_IDLE_TIMEOUT_SECONDS:g} 秒"
            )
        elif elapsed > STREAM_ABSOLUTE_TIMEOUT_SECONDS:
            timeout_reason = (
                f"整次模型请求超过绝对上限 {STREAM_ABSOLUTE_TIMEOUT_SECONDS:g} 秒"
            )

        if timeout_reason:
            stream_error = timeout_reason
            print(f"  ⚠ {timeout_reason}，停止等待当前流并尝试异步报告兜底或重试")
            stop_event.set()
            try:
                resp.close()
            except Exception:
                pass
            break

        try:
            event_type, payload = event_queue.get(
                timeout=max(0.1, float(STREAM_QUEUE_POLL_INTERVAL_SECONDS))
            )
        except queue.Empty:
            now = time.time()
            if now - last_progress_print >= STREAM_PROGRESS_PRINT_INTERVAL_SECONDS:
                _print_stream_progress(
                    task_label=task_label,
                    elapsed=now - start_time,
                    since_last_data=now - last_data_time,
                    first_data_seconds=(
                        first_data_time - start_time
                        if first_data_time is not None
                        else None
                    ),
                    sse_line_count=sse_line_count,
                    reasoning_chars=sum(len(value) for value in reasoning_parts),
                    content_chars=sum(len(value) for value in content_parts),
                    report_url=report_url,
                )
                last_progress_print = now
            continue

        if event_type == "error":
            stream_error = f"{type(payload).__name__}: {payload}"
            print(f"  ⚠ 流读取线程异常：{stream_error}")
            break

        if event_type == "eof":
            break

        raw_line = payload
        if raw_line is None:
            continue

        line = (
            raw_line.decode("utf-8", errors="replace")
            if isinstance(raw_line, bytes)
            else str(raw_line)
        )

        now = time.time()
        last_data_time = now
        if first_data_time is None:
            first_data_time = now
            print(
                f"  ✓ 收到首个流数据，用时 "
                f"{first_data_time - start_time:.1f} 秒"
            )

        raw_lines.append(line)
        capture_report_url(line)

        if DEBUG_PRINT_RAW_SSE and line:
            print(f"\n[SSE 原始数据] {line}", flush=True)

        if not line or not line.startswith("data:"):
            continue

        is_sse = True
        sse_line_count += 1
        data_str = line[5:].strip()
        capture_report_url(data_str)

        if not data_str:
            continue
        if data_str == "[DONE]":
            saw_done = True
            print("\n  ✓ 已收到 SSE [DONE]")
            break

        try:
            chunk = json.loads(data_str)
        except json.JSONDecodeError:
            append_content(data_str)
            continue

        capture_report_url(chunk)

        choices = chunk.get("choices") if isinstance(chunk, dict) else None
        if isinstance(choices, list) and choices:
            first = choices[0]
            if isinstance(first, dict):
                current_finish = first.get("finish_reason")
                if current_finish is not None:
                    finish_reason = str(current_finish)
                    print(f"\n  ℹ finish_reason={finish_reason}")

                delta = first.get("delta") or {}
                message = first.get("message") or {}

                if isinstance(delta, dict):
                    reasoning_piece = response_content_to_text(
                        delta.get("reasoning_content")
                    )
                    content_piece = response_content_to_text(delta.get("content"))
                    capture_report_url(reasoning_piece, content_piece)
                    append_reasoning(reasoning_piece)
                    append_content(content_piece)

                if isinstance(message, dict):
                    reasoning_piece = response_content_to_text(
                        message.get("reasoning_content")
                    )
                    content_piece = response_content_to_text(message.get("content"))
                    capture_report_url(reasoning_piece, content_piece)
                    append_reasoning(reasoning_piece)
                    append_content(content_piece)
        elif isinstance(chunk, dict):
            reasoning_piece = response_content_to_text(chunk.get("reasoning_content"))
            content_piece = (
                response_content_to_text(chunk.get("content"))
                + response_content_to_text(chunk.get("output_text"))
            )
            capture_report_url(reasoning_piece, content_piece)
            append_reasoning(reasoning_piece)
            append_content(content_piece)

        now = time.time()
        if now - last_progress_print >= STREAM_PROGRESS_PRINT_INTERVAL_SECONDS:
            _print_stream_progress(
                task_label=task_label,
                elapsed=now - start_time,
                since_last_data=now - last_data_time,
                first_data_seconds=(
                    first_data_time - start_time
                    if first_data_time is not None
                    else None
                ),
                sse_line_count=sse_line_count,
                reasoning_chars=sum(len(value) for value in reasoning_parts),
                content_chars=sum(len(value) for value in content_parts),
                report_url=report_url,
            )
            last_progress_print = now

    stop_event.set()

    if not is_sse:
        raw_body = "\n".join(raw_lines)
        capture_report_url(raw_body)
        try:
            body = json.loads(raw_body)
        except json.JSONDecodeError:
            if raw_body:
                content_parts = [raw_body]
        else:
            capture_report_url(body)
            choices = body.get("choices") if isinstance(body, dict) else None
            if isinstance(choices, list) and choices:
                first = choices[0]
                if isinstance(first, dict):
                    message = first.get("message") or {}
                    if isinstance(message, dict):
                        append_reasoning(
                            response_content_to_text(message.get("reasoning_content"))
                        )
                        append_content(
                            response_content_to_text(message.get("content"))
                        )
            elif isinstance(body, dict):
                append_reasoning(
                    response_content_to_text(body.get("reasoning_content"))
                )
                append_content(response_content_to_text(body.get("content")))
                append_content(response_content_to_text(body.get("output_text")))

    if DEBUG_PRINT_STREAM and content_parts:
        print(flush=True)

    elapsed_seconds = time.time() - start_time
    first_data_seconds = (
        first_data_time - start_time
        if first_data_time is not None
        else None
    )

    print(
        f"  ■ 流读取结束：总耗时 {elapsed_seconds:.1f} 秒；"
        f"SSE={is_sse}；DONE={saw_done}；"
        f"finish_reason={finish_reason or '无'}；"
        f"推理 {sum(len(value) for value in reasoning_parts)} 字；"
        f"正式输出 {sum(len(value) for value in content_parts)} 字；"
        f"stream_error={stream_error or '无'}；"
        f"异步报告={report_url or '无'}"
    )

    return ModelResponse(
        content_text="".join(content_parts),
        reasoning_text="".join(reasoning_parts),
        finish_reason=finish_reason,
        saw_done=saw_done,
        is_sse=is_sse,
        stream_error=stream_error,
        report_url=report_url,
        elapsed_seconds=elapsed_seconds,
        first_data_seconds=first_data_seconds,
        sse_line_count=sse_line_count,
    )


def post_stream_with_progress(
    session: requests.Session,
    url: str,
    headers: dict[str, str],
    payload: dict[str, Any],
    task_label: str,
) -> requests.Response:
    """后台建立 HTTP 请求，主线程持续打印等待响应头的状态。"""
    result_queue: queue.Queue[tuple[str, Any]] = queue.Queue()

    def post_worker() -> None:
        try:
            response = session.post(
                url,
                headers=headers,
                json=payload,
                timeout=REQUEST_TIMEOUT,
                stream=True,
            )
            result_queue.put(("response", response))
        except Exception as exc:
            result_queue.put(("error", exc))

    worker = threading.Thread(
        target=post_worker,
        name="font-mapping-http-connect",
        daemon=True,
    )
    worker.start()

    start_time = time.time()
    last_progress_print = start_time

    while True:
        try:
            event_type, payload_value = result_queue.get(
                timeout=max(0.1, float(STREAM_QUEUE_POLL_INTERVAL_SECONDS))
            )
        except queue.Empty:
            now = time.time()
            elapsed = now - start_time

            if elapsed > RESPONSE_HEADER_ABSOLUTE_TIMEOUT_SECONDS:
                try:
                    session.close()
                except Exception:
                    pass
                raise TimeoutError(
                    f"等待 API 响应头超过绝对上限 "
                    f"{RESPONSE_HEADER_ABSOLUTE_TIMEOUT_SECONDS:g} 秒"
                )

            if now - last_progress_print >= STREAM_PROGRESS_PRINT_INTERVAL_SECONDS:
                print(
                    f"  📡 {task_label}正在等待 API 响应头："
                    f"已等待 {elapsed:.1f} 秒；"
                    f"连接超时 {REQUEST_CONNECT_TIMEOUT_SECONDS:g} 秒；"
                    f"底层读取超时 {STREAM_SOCKET_READ_TIMEOUT_SECONDS:g} 秒；"
                    f"响应头绝对上限 {RESPONSE_HEADER_ABSOLUTE_TIMEOUT_SECONDS:g} 秒"
                )
                last_progress_print = now
            continue

        if event_type == "error":
            raise payload_value

        if event_type == "response":
            return payload_value

        raise RuntimeError(f"未知 HTTP 建连事件：{event_type}")


def call_model_once(
    prompt: str,
    task_label: str,
    work_dir: Path,
    round_num: int,
    prompt_sha256: str,
) -> ModelResponse:
    current_key = key_manager.get_current_key()
    if not current_key:
        raise RuntimeError("没有可用的 API Key")

    key_num, key_total, key_fails = key_manager.get_current_info()
    print(
        f"\n=== {task_label}，Key #{key_num}/{key_total}，"
        f"连续失败 {key_fails} ==="
    )
    print(
        f"  提示词字符数：{len(prompt)}；"
        f"SHA256：{prompt_sha256[:16]}...；"
        f"首数据超时：{STREAM_FIRST_DATA_TIMEOUT_SECONDS:g} 秒；"
        f"空闲超时：{STREAM_IDLE_TIMEOUT_SECONDS:g} 秒；"
        f"绝对超时：{STREAM_ABSOLUTE_TIMEOUT_SECONDS:g} 秒"
    )

    headers = {
        "Authorization": f"Bearer {current_key}",
        "Content-Type": "application/json",
    }
    payload = {
        "model": MODEL,
        "stream": True,
        "messages": [{"role": "user", "content": prompt}],
        "temperature": 0,
    }

    wait_global_request_slot()
    session = build_session()
    response: requests.Response | None = None
    request_start = time.time()

    try:
        print("  → 正在建立 API 连接并等待响应头……")
        response = post_stream_with_progress(
            session=session,
            url=BASE_URL.rstrip("/"),
            headers=headers,
            payload=payload,
            task_label=task_label,
        )
        connect_elapsed = time.time() - request_start
        print(
            f"  ✓ API 连接建立：HTTP {response.status_code}；"
            f"耗时 {connect_elapsed:.1f} 秒"
        )

        if response.status_code != 200:
            error_text = response.text[:1000]
            raise RuntimeError(f"HTTP {response.status_code}：{error_text}")

        header_text = "\n".join(
            f"{key}: {value}"
            for key, value in response.headers.items()
        )
        header_report_url = extract_async_report_url(header_text)
        if header_report_url:
            save_captured_async_report_url(
                work_dir=work_dir,
                round_num=round_num,
                report_url=header_report_url,
                prompt_sha256=prompt_sha256,
                task_label=task_label,
            )
            print(f"  🔗 已从响应头捕获异步报告页：{header_report_url}")

        result = read_model_response(
            response,
            task_label=task_label,
            work_dir=work_dir,
            round_num=round_num,
            prompt_sha256=prompt_sha256,
        )
        if result.report_url is None and header_report_url:
            result.report_url = header_report_url

        key_manager.report_success()
        return result
    except Exception:
        key_manager.report_failure()
        raise
    finally:
        if response is not None:
            try:
                response.close()
            except Exception:
                pass
        session.close()


def is_explicit_truncation(result: ModelResponse) -> bool:
    reason = (result.finish_reason or "").strip().lower()
    return reason in {
        "length",
        "max_tokens",
        "max_output_tokens",
        "token_limit",
    }


def stream_looks_incomplete(result: ModelResponse) -> bool:
    return bool(
        result.stream_error
        or (result.is_sse and not result.saw_done)
        or is_explicit_truncation(result)
    )


# ============================================================
# 11. 严格解析模型输出与异步报告恢复
# ============================================================


def find_single_block(text: str, start_marker: str, end_marker: str) -> tuple[str, tuple[int, int]]:
    if text.count(start_marker) != 1:
        raise ValueError(f"{start_marker} 必须且只能出现一次")
    if text.count(end_marker) != 1:
        raise ValueError(f"{end_marker} 必须且只能出现一次")

    start = text.index(start_marker)
    end = text.index(end_marker, start + len(start_marker))
    if end <= start:
        raise ValueError(f"标记顺序错误：{start_marker} / {end_marker}")

    content = text[start + len(start_marker):end]
    if content.startswith("\r\n"):
        content = content[2:]
    elif content.startswith("\n") or content.startswith("\r"):
        content = content[1:]
    if content.endswith("\r\n"):
        content = content[:-2]
    elif content.endswith("\n") or content.endswith("\r"):
        content = content[:-1]

    return content, (start, end + len(end_marker))


def validate_download_url(value: str, key: str) -> str:
    url = value.strip()
    parsed = urlparse(url)
    if parsed.scheme.lower() not in {"http", "https"} or not parsed.netloc:
        raise ValueError(f"映射 {key} 的 download_url 不是有效 HTTP(S) URL：{url}")
    return url


def _is_strict_nonnegative_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _is_strict_positive_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def validate_model_font_validation_report(
    payload: Any,
    mappings: dict[str, FontMappingDecision | None],
) -> dict[str, Any]:
    if not isinstance(payload, dict):
        raise ValueError("字体本地校验报告顶层必须是 JSON 对象")

    required_top_fields = {"version", "status", "environment", "fonts"}
    if set(payload) != required_top_fields:
        raise ValueError(
            "字体本地校验报告顶层字段不符合协议；"
            f"缺少={sorted(required_top_fields - set(payload))}；"
            f"多余={sorted(set(payload) - required_top_fields)}"
        )
    if payload.get("version") != 1:
        raise ValueError("字体本地校验报告 version 必须为 1")
    if payload.get("status") != "passed":
        raise ValueError("字体本地校验报告 status 必须为 passed")

    environment = payload.get("environment")
    if not isinstance(environment, dict):
        raise ValueError("字体本地校验报告 environment 必须是对象")
    required_environment_fields = {
        "python_version",
        "pymupdf_version",
        "fonttools_version",
    }
    if set(environment) != required_environment_fields:
        raise ValueError(
            "字体本地校验报告 environment 字段不符合协议；"
            f"缺少={sorted(required_environment_fields - set(environment))}；"
            f"多余={sorted(set(environment) - required_environment_fields)}"
        )
    for field_name in required_environment_fields:
        if not isinstance(environment.get(field_name), str) or not environment[field_name].strip():
            raise ValueError(f"字体本地校验报告 environment.{field_name} 必须是非空字符串")
    expected_pymupdf_version = get_pymupdf_version()
    if environment["pymupdf_version"].strip() != expected_pymupdf_version:
        raise ValueError(
            "模型字体校验使用的 PyMuPDF 版本与生产环境不一致；"
            f"期望={expected_pymupdf_version}；"
            f"实际={environment['pymupdf_version'].strip()}"
        )

    expected_fonts: dict[str, str] = {}
    for key, decision in mappings.items():
        if decision is None:
            continue
        normalized_name = decision.target_font_file.casefold()
        previous_url = expected_fonts.get(normalized_name)
        if previous_url is not None and previous_url != decision.download_url:
            raise ValueError(
                "多个映射键把同一目标字体文件名映射到不同 URL："
                f"{decision.target_font_file}"
            )
        expected_fonts[normalized_name] = decision.download_url

    fonts = payload.get("fonts")
    if not isinstance(fonts, dict):
        raise ValueError("字体本地校验报告 fonts 必须是对象")
    actual_by_normalized: dict[str, tuple[str, Any]] = {}
    for font_name, font_report in fonts.items():
        if not isinstance(font_name, str) or not font_name.strip():
            raise ValueError("字体本地校验报告 fonts 中存在空字体文件名")
        normalized_name = font_name.casefold()
        if normalized_name in actual_by_normalized:
            raise ValueError(f"字体本地校验报告中重复字体文件名：{font_name}")
        actual_by_normalized[normalized_name] = (font_name, font_report)

    missing_fonts = sorted(set(expected_fonts) - set(actual_by_normalized))
    extra_fonts = sorted(set(actual_by_normalized) - set(expected_fonts))
    if missing_fonts or extra_fonts:
        raise ValueError(
            "字体本地校验报告 fonts 键集合与映射引用的不同字体文件不一致；"
            f"缺少={missing_fonts}；多余={extra_fonts}"
        )

    required_font_fields = {
        "download_url",
        "sha256",
        "size_bytes",
        "unicode_cmap_scanned",
        "ambiguous_glyph_count",
        "ambiguous_standard_codepoint_count",
        "insert_text_exact_roundtrip",
        "insert_textbox_exact_roundtrip",
        "subset_fonts_tested",
        "compatibility_ideographs_found_after_extract",
        "result",
    }
    sha256_pattern = re.compile(r"[0-9a-f]{64}")

    for normalized_name, expected_url in expected_fonts.items():
        display_name, font_report = actual_by_normalized[normalized_name]
        if not isinstance(font_report, dict):
            raise ValueError(f"字体校验项 {display_name} 必须是对象")
        if set(font_report) != required_font_fields:
            raise ValueError(
                f"字体校验项 {display_name} 字段不符合协议；"
                f"缺少={sorted(required_font_fields - set(font_report))}；"
                f"多余={sorted(set(font_report) - required_font_fields)}"
            )
        if font_report.get("download_url") != expected_url:
            raise ValueError(
                f"字体校验项 {display_name} 的 download_url 与映射不一致；"
                f"映射={expected_url}；报告={font_report.get('download_url')}"
            )
        sha256_value = font_report.get("sha256")
        if not isinstance(sha256_value, str) or not sha256_pattern.fullmatch(sha256_value):
            raise ValueError(f"字体校验项 {display_name} 的 sha256 必须是 64 位小写十六进制")
        if not _is_strict_positive_int(font_report.get("size_bytes")):
            raise ValueError(f"字体校验项 {display_name} 的 size_bytes 必须是正整数")
        if font_report.get("unicode_cmap_scanned") is not True:
            raise ValueError(f"字体校验项 {display_name} 未完成全部 Unicode cmap 扫描")
        if not _is_strict_nonnegative_int(font_report.get("ambiguous_glyph_count")):
            raise ValueError(f"字体校验项 {display_name} 的 ambiguous_glyph_count 无效")
        if not _is_strict_nonnegative_int(
            font_report.get("ambiguous_standard_codepoint_count")
        ):
            raise ValueError(
                f"字体校验项 {display_name} 的 ambiguous_standard_codepoint_count 无效"
            )
        if font_report.get("insert_text_exact_roundtrip") is not True:
            raise ValueError(f"字体校验项 {display_name} 的 insert_text 精确往返未通过")
        if font_report.get("insert_textbox_exact_roundtrip") is not True:
            raise ValueError(f"字体校验项 {display_name} 的 insert_textbox 精确往返未通过")
        if font_report.get("subset_fonts_tested") is not True:
            raise ValueError(f"字体校验项 {display_name} 未测试字体子集化")
        if font_report.get("compatibility_ideographs_found_after_extract") is not False:
            raise ValueError(f"字体校验项 {display_name} 提取结果含 CJK 兼容表意文字")
        if font_report.get("result") != "pass":
            raise ValueError(f"字体校验项 {display_name} result 必须为 pass")

    return payload


def parse_mapping_response(
    text: str,
    expected_keys: set[str],
) -> tuple[
    str,
    dict[str, FontMappingDecision | None],
    dict[str, Any],
]:
    commands_text, commands_span = find_single_block(text, FONT_DOWNLOAD_START, FONT_DOWNLOAD_END)
    validation_text, validation_span = find_single_block(
        text,
        FONT_VALIDATION_START,
        FONT_VALIDATION_END,
    )
    mapping_text, mapping_span = find_single_block(text, FONT_MAPPING_START, FONT_MAPPING_END)

    if not (commands_span[0] < validation_span[0] < mapping_span[0]):
        raise ValueError("三个输出区块顺序必须是下载命令、校验报告、字体映射表")

    outside = text
    for start, end in sorted(
        [commands_span, validation_span, mapping_span],
        reverse=True,
    ):
        outside = outside[:start] + outside[end:]
    if outside.strip():
        raise ValueError(f"三个规定区块之外存在额外内容：{outside.strip()[:300]}")

    normalized_commands = commands_text.strip()
    normalized_validation = validation_text.strip()
    normalized_mapping = mapping_text.strip()
    for marker in (
        PDF_DOWNLOAD_UNAVAILABLE_MARKER,
        LOCAL_VALIDATION_TOOL_UNAVAILABLE_MARKER,
    ):
        marker_hits = (
            normalized_commands == marker,
            normalized_validation == marker,
            normalized_mapping == marker,
        )
        if any(marker_hits):
            if not all(marker_hits):
                raise ValueError(
                    "使用特殊标记时，三个区块必须同时且只包含同一标记："
                    f"{marker}"
                )
            raise RetriableModelMarker(marker)

    try:
        payload = json.loads(mapping_text)
    except json.JSONDecodeError as exc:
        raise ValueError(f"字体映射表不是合法 JSON：{exc}") from exc

    if not isinstance(payload, dict):
        raise ValueError("字体映射 JSON 顶层必须是对象")
    if payload.get("version") != 3:
        raise ValueError("字体映射 JSON version 必须为 3")

    mappings = payload.get("mappings")
    if not isinstance(mappings, dict):
        raise ValueError("字体映射 JSON 的 mappings 必须是对象")

    actual_keys = set(mappings)
    missing = sorted(expected_keys - actual_keys)
    extra = sorted(actual_keys - expected_keys)
    if missing or extra:
        raise ValueError(f"映射键集合不一致；缺少={missing}；多余={extra}")

    validated: dict[str, FontMappingDecision | None] = {}
    allowed_exts = {".otf", ".ttf", ".ttc", ".otc"}

    for key in sorted(expected_keys, key=lambda value: value.casefold()):
        value = mappings[key]

        if value is None:
            validated[key] = None
            continue

        if not isinstance(value, dict):
            raise ValueError(f"映射 {key} 的值必须是对象或 null")

        allowed_fields = {"target_font_file", "download_url"}
        extra_fields = sorted(set(value) - allowed_fields)
        missing_fields = sorted(allowed_fields - set(value))
        if extra_fields or missing_fields:
            raise ValueError(
                f"映射 {key} 字段不符合协议；缺少={missing_fields}；多余={extra_fields}"
            )

        target_font_file = value.get("target_font_file")
        download_url = value.get("download_url")

        if not isinstance(target_font_file, str) or not target_font_file.strip():
            raise ValueError(f"映射 {key} 的 target_font_file 必须是非空字符串")
        filename = target_font_file.strip()
        path = Path(filename)
        if path.name != filename or path.is_absolute():
            raise ValueError(f"映射 {key} 必须只填写字体文件名，不得含目录：{filename}")
        if path.suffix.lower() not in allowed_exts:
            raise ValueError(f"映射 {key} 的字体扩展名不允许：{filename}")
        if not isinstance(download_url, str) or not download_url.strip():
            raise ValueError(f"映射 {key} 的 download_url 必须是非空字符串")
        validated_url = validate_download_url(download_url, key)

        validated[key] = FontMappingDecision(
            target_font_file=filename,
            download_url=validated_url,
        )

    try:
        validation_payload = json.loads(validation_text)
    except json.JSONDecodeError as exc:
        raise ValueError(f"字体本地校验报告不是合法 JSON：{exc}") from exc
    validated_report = validate_model_font_validation_report(
        validation_payload,
        validated,
    )

    return commands_text, validated, validated_report


def try_parse_model_candidates(
    result: ModelResponse,
    expected_keys: set[str],
) -> tuple[
    str,
    dict[str, FontMappingDecision | None],
    dict[str, Any],
    str,
]:
    errors: list[str] = []
    for label, candidate in (
        ("content", result.content_text),
        ("content+reasoning", result.merged_text),
        ("reasoning", result.reasoning_text),
    ):
        if not candidate:
            continue
        try:
            commands, mappings, validation_report = parse_mapping_response(
                candidate,
                expected_keys,
            )
            return commands, mappings, validation_report, candidate
        except RetriableModelMarker:
            raise
        except Exception as exc:
            errors.append(f"{label}: {type(exc).__name__}: {exc}")

    raise ValueError("；".join(errors) if errors else "模型响应为空")


def parse_async_report_mapping_content(
    content: str,
    expected_keys: set[str],
) -> tuple[
    str,
    dict[str, FontMappingDecision | None],
    dict[str, Any],
    str,
]:
    commands, mappings, validation_report = parse_mapping_response(
        content,
        expected_keys,
    )
    return commands, mappings, validation_report, content


def parse_mapping_with_async_report_fallback(
    result: ModelResponse,
    expected_keys: set[str],
    work_dir: Path,
    round_num: int,
    prompt_sha256: str,
    task_label: str,
) -> tuple[
    str,
    dict[str, FontMappingDecision | None],
    dict[str, Any],
    str,
    str,
]:
    api_parse_error: Exception | None = None

    try:
        commands, mappings, validation_report, validated_raw = try_parse_model_candidates(
            result,
            expected_keys,
        )
        clear_async_report_state(work_dir, round_num)
        return commands, mappings, validation_report, validated_raw, "API 流式内容"
    except RetriableModelMarker:
        clear_async_report_state(work_dir, round_num)
        raise
    except Exception as exc:
        api_parse_error = exc

    diagnostics = (
        f"finish_reason={result.finish_reason or '无'}；"
        f"DONE={result.saw_done}；"
        f"stream_error={result.stream_error or '无'}；"
        f"content={len(result.content_text)} 字；"
        f"reasoning={len(result.reasoning_text)} 字"
    )
    print(f"  ⚠ API 内容未通过协议解析：{api_parse_error}")
    print(f"  ℹ 流诊断：{diagnostics}")

    if not result.report_url:
        raise ValueError(
            "API 流式内容无法通过字体映射协议解析，且未找到异步报告 URL。\n"
            f"解析错误：{api_parse_error}\n"
            f"流诊断：{diagnostics}"
        )

    report_state = load_async_report_state(
        work_dir,
        round_num,
        expected_prompt_sha256=prompt_sha256,
    )
    started_at_epoch: float | None = None
    if report_state:
        try:
            started_at_epoch = float(report_state.get("started_at_epoch"))
        except (TypeError, ValueError):
            started_at_epoch = None

    report_result = wait_for_async_report(
        report_url=result.report_url,
        work_dir=work_dir,
        round_num=round_num,
        prompt_sha256=prompt_sha256,
        task_label=task_label,
        started_at_epoch=started_at_epoch,
    )

    if report_result.status in {"error", "failed", "cancelled"}:
        clear_async_report_state(work_dir, round_num)
        raise ValueError(
            "异步报告页返回错误。\n"
            f"状态：{report_result.status}\n"
            f"错误：{report_result.error_message or '无详细信息'}"
        )

    if report_result.status == "timeout":
        clear_async_report_state(work_dir, round_num)
        raise ValueError(
            "异步报告页等待超时。\n"
            f"错误：{report_result.error_message or '无详细信息'}"
        )

    if report_result.status != "completed":
        clear_async_report_state(work_dir, round_num)
        raise ValueError(f"异步报告页返回未处理状态：{report_result.status}")

    try:
        (
            commands,
            mappings,
            validation_report,
            validated_raw,
        ) = parse_async_report_mapping_content(
            report_result.content,
            expected_keys,
        )
    except RetriableModelMarker:
        clear_async_report_state(work_dir, round_num)
        raise
    except Exception as report_parse_error:
        clear_async_report_state(work_dir, round_num)
        raise ValueError(
            "异步报告页已 completed，但完整内容仍无法通过字体映射协议解析。\n"
            f"API 解析错误：{api_parse_error}\n"
            f"报告页解析错误：{report_parse_error}"
        ) from report_parse_error

    return (
        commands,
        mappings,
        validation_report,
        validated_raw,
        "异步报告页 completed 内容",
    )


def try_resume_validated_mapping_round(
    work_dir: Path,
    round_num: int,
    prompt_sha256: str,
    expected_keys: set[str],
) -> tuple[
    str,
    dict[str, FontMappingDecision | None],
    dict[str, Any],
    str,
    str,
] | None:
    """
    复用已经通过严格协议校验的本地轮次结果。

    只有同时满足以下条件才复用：
    1. validated 文件存在且非空；
    2. 至少一个对应 meta 文件的 prompt_sha256 与本轮完全一致；
    3. validated 内容仍能按本轮 expected_keys 严格解析。
    """
    validated_path = (
        work_dir
        / f"01_round_{round_num:03d}_model_response_validated.txt"
    )
    if not validated_path.is_file() or validated_path.stat().st_size <= 0:
        return None

    meta_paths = sorted(
        work_dir.glob(
            f"01_round_{round_num:03d}_model_response_meta*.json"
        ),
        key=lambda path: path.stat().st_mtime_ns,
        reverse=True,
    )

    matching_meta_path: Path | None = None
    for meta_path in meta_paths:
        try:
            meta = json.loads(
                meta_path.read_text(encoding="utf-8-sig")
            )
        except Exception:
            continue

        stored_prompt_sha256 = str(
            meta.get("prompt_sha256") or ""
        ).strip().lower()
        if stored_prompt_sha256 == prompt_sha256.lower():
            matching_meta_path = meta_path
            break

    if matching_meta_path is None:
        print(
            f"  ℹ 第 {round_num} 轮存在本地 validated 文件，"
            "但没有找到提示词 SHA256 一致的 meta，不予复用"
        )
        return None

    try:
        validated_raw = validated_path.read_text(encoding="utf-8-sig")
        commands, mappings, validation_report = parse_mapping_response(
            validated_raw,
            expected_keys,
        )
    except RetriableModelMarker as exc:
        print(
            f"  ℹ 第 {round_num} 轮本地 validated 文件只包含可重试标记 "
            f"{exc.marker}，不予复用"
        )
        clear_async_report_state(work_dir, round_num)
        return None
    except Exception as exc:
        print(
            f"  ⚠ 第 {round_num} 轮本地 validated 结果重新校验失败，"
            f"将继续检查异步断点或重新请求：{type(exc).__name__}: {exc}"
        )
        return None

    clear_async_report_state(work_dir, round_num)
    print(
        f"  ✓ 复用第 {round_num} 轮本地已验证结果："
        f"{validated_path}\n"
        f"    匹配元数据：{matching_meta_path.name}\n"
        f"    提示词 SHA256：{prompt_sha256}"
    )
    return (
        commands,
        mappings,
        validation_report,
        validated_raw,
        "断点续传：本地已验证模型结果",
    )


def try_resume_mapping_round(
    work_dir: Path,
    round_num: int,
    prompt_sha256: str,
    task_label: str,
    expected_keys: set[str],
) -> tuple[
    str,
    dict[str, FontMappingDecision | None],
    dict[str, Any],
    str,
    str,
] | None:
    if not ASYNC_REPORT_RESUME_ENABLED:
        return None

    state = load_async_report_state(
        work_dir,
        round_num,
        expected_prompt_sha256=prompt_sha256,
    )
    if not state:
        return None

    report_url = str(state.get("report_url") or "").strip()
    status = str(state.get("status") or "unknown").strip().lower()
    try:
        started_at_epoch = float(state.get("started_at_epoch"))
    except (TypeError, ValueError):
        started_at_epoch = time.time()

    remaining_seconds = get_async_report_remaining_seconds(started_at_epoch)
    print(
        f"  ♻ 检测到第 {round_num} 轮异步报告断点：\n"
        f"    URL：{report_url}\n"
        f"    状态：{status}\n"
        f"    首次记录：{format_local_timestamp(started_at_epoch)}\n"
        f"    剩余等待：{remaining_seconds:.1f} 秒"
    )

    if status in {"error", "failed", "cancelled", "timeout"}:
        print(f"  ⚠ 旧异步报告已进入 {status} 状态，将重新请求模型")
        clear_async_report_state(work_dir, round_num)
        return None

    completed_content_path_value = str(
        state.get("completed_content_path") or ""
    ).strip()
    if status == "completed" and completed_content_path_value:
        completed_content_path = Path(completed_content_path_value).expanduser()
        if completed_content_path.is_file() and completed_content_path.stat().st_size > 0:
            completed_content = completed_content_path.read_text(encoding="utf-8-sig")
            try:
                (
                    commands,
                    mappings,
                    validation_report,
                    validated_raw,
                ) = parse_async_report_mapping_content(
                    completed_content,
                    expected_keys,
                )
                print(
                    f"  ✓ 直接复用第 {round_num} 轮已保存的异步报告完整内容："
                    f"{completed_content_path}"
                )
                return (
                    commands,
                    mappings,
                    validation_report,
                    validated_raw,
                    "断点续传：本地异步报告 completed 内容",
                )
            except RetriableModelMarker as exc:
                print(
                    f"  ℹ 本地 completed 内容为可重试标记 {exc.marker}，"
                    "将清理状态并重新请求模型"
                )
                clear_async_report_state(work_dir, round_num)
                return None
            except Exception as exc:
                print(
                    f"  ⚠ 本地 completed 内容无法解析，将重新访问报告页：{exc}"
                )

    if remaining_seconds <= 0:
        print("  ⚠ 旧异步任务已超过总等待时间，将清理状态并重新请求模型")
        clear_async_report_state(work_dir, round_num)
        return None

    report_result = wait_for_async_report(
        report_url=report_url,
        work_dir=work_dir,
        round_num=round_num,
        prompt_sha256=prompt_sha256,
        task_label=task_label,
        started_at_epoch=started_at_epoch,
    )

    if report_result.status == "completed":
        try:
            (
                commands,
                mappings,
                validation_report,
                validated_raw,
            ) = parse_async_report_mapping_content(
                report_result.content,
                expected_keys,
            )
        except RetriableModelMarker as exc:
            print(
                f"  ℹ 断点报告返回可重试标记 {exc.marker}，"
                "将清理状态并重新请求模型"
            )
            clear_async_report_state(work_dir, round_num)
            return None
        except Exception as exc:
            print(
                f"  ⚠ 断点报告已 completed，但内容无法解析：{exc}；"
                "将清理状态并重新请求模型"
            )
            clear_async_report_state(work_dir, round_num)
            return None

        return (
            commands,
            mappings,
            validation_report,
            validated_raw,
            "断点续传：异步报告 completed 内容",
        )

    print(
        f"  ⚠ 断点报告状态为 {report_result.status}，"
        "将清理状态并重新请求模型"
    )
    clear_async_report_state(work_dir, round_num)
    return None


def request_mapping_round(
    prompt: str,
    expected_keys: set[str],
    work_dir: Path,
    round_num: int,
    task_label: str,
    allow_validated_resume: bool = True,
    max_attempts: int | None = None,
) -> tuple[
    str,
    dict[str, FontMappingDecision | None],
    dict[str, Any],
    str,
]:
    prompt_name = (
        "00_font_mapping_prompt.txt"
        if round_num == 1
        else f"00_font_mapping_prompt_round_{round_num:03d}.txt"
    )
    (work_dir / prompt_name).write_text(prompt, encoding="utf-8")
    prompt_sha256 = hashlib.sha256(prompt.encode("utf-8")).hexdigest()

    if allow_validated_resume:
        validated_resumed = try_resume_validated_mapping_round(
            work_dir=work_dir,
            round_num=round_num,
            prompt_sha256=prompt_sha256,
            expected_keys=expected_keys,
        )
        if validated_resumed is not None:
            (
                commands_text,
                decisions,
                validation_report,
                validated_raw,
                reply_source,
            ) = validated_resumed
            print(f"  ✓ 本轮采用的回复来源：{reply_source}")
            return commands_text, decisions, validation_report, validated_raw

    resumed = try_resume_mapping_round(
        work_dir=work_dir,
        round_num=round_num,
        prompt_sha256=prompt_sha256,
        task_label=task_label,
        expected_keys=expected_keys,
    )
    if resumed is not None:
        (
            commands_text,
            decisions,
            validation_report,
            validated_raw,
            reply_source,
        ) = resumed
        print(f"  ✓ 本轮采用的回复来源：{reply_source}")
        return commands_text, decisions, validation_report, validated_raw

    retry_limit = RETRY_COUNT if max_attempts is None else max(1, int(max_attempts))
    for attempt in range(1, retry_limit + 1):
        if attempt > 1:
            print(f"{task_label}第 {attempt} 次重试，等待 {RETRY_DELAY} 秒……")
            time.sleep(RETRY_DELAY)

        try:
            response = call_model_once(
                prompt=prompt,
                task_label=task_label,
                work_dir=work_dir,
                round_num=round_num,
                prompt_sha256=prompt_sha256,
            )
            attempt_suffix = "" if attempt == 1 else f"_retry_{attempt}"
            prefix = f"01_round_{round_num:03d}"

            (work_dir / f"{prefix}_model_response_content{attempt_suffix}.txt").write_text(
                response.content_text,
                encoding="utf-8",
            )
            (work_dir / f"{prefix}_model_response_reasoning{attempt_suffix}.txt").write_text(
                response.reasoning_text,
                encoding="utf-8",
            )
            (work_dir / f"{prefix}_model_response_meta{attempt_suffix}.json").write_text(
                json.dumps(
                    {
                        "finish_reason": response.finish_reason,
                        "saw_done": response.saw_done,
                        "is_sse": response.is_sse,
                        "stream_error": response.stream_error,
                        "report_url": response.report_url,
                        "elapsed_seconds": response.elapsed_seconds,
                        "first_data_seconds": response.first_data_seconds,
                        "sse_line_count": response.sse_line_count,
                        "content_chars": len(response.content_text),
                        "reasoning_chars": len(response.reasoning_text),
                        "prompt_sha256": prompt_sha256,
                    },
                    ensure_ascii=False,
                    indent=2,
                ),
                encoding="utf-8",
            )

            if is_explicit_truncation(response):
                print(
                    f"  ⚠ 模型明确报告截断：finish_reason={response.finish_reason}；"
                    "将优先尝试异步报告完整内容"
                )
            elif response.is_sse and not response.saw_done:
                print(
                    "  ⚠ SSE 未收到 [DONE]；将根据协议完整性决定是否启用异步报告兜底"
                )
            if response.stream_error:
                print(
                    f"  ⚠ 流读取存在错误：{response.stream_error}；"
                    "将根据协议完整性和异步报告决定是否重试"
                )

            (
                commands_text,
                decisions,
                validation_report,
                validated_raw,
                reply_source,
            ) = parse_mapping_with_async_report_fallback(
                result=response,
                expected_keys=expected_keys,
                work_dir=work_dir,
                round_num=round_num,
                prompt_sha256=prompt_sha256,
                task_label=task_label,
            )

            (work_dir / f"{prefix}_model_response_validated.txt").write_text(
                validated_raw,
                encoding="utf-8",
            )
            (work_dir / f"{prefix}_model_font_validation_report.json").write_text(
                json.dumps(validation_report, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
            print(f"  ✓ 本轮采用的回复来源：{reply_source}")
            return commands_text, decisions, validation_report, validated_raw

        except RetriableModelMarker as exc:
            marker_path = (
                work_dir
                / f"01_round_{round_num:03d}_special_marker_"
                f"{attempt:04d}_{int(time.time())}.txt"
            )
            marker_path.write_text(exc.marker, encoding="utf-8")
            clear_async_report_state(work_dir, round_num)
            print(
                f"↻ {task_label}返回可重试特殊标记 {exc.marker}；"
                "本轮不接受映射，继续重新请求"
            )
            key_manager.report_failure()
            continue
        except Exception as exc:
            print(f"✗ {task_label}失败：{type(exc).__name__}: {exc}")
            key_manager.report_failure()
            continue

    raise RuntimeError(f"{task_label}在 {retry_limit} 次尝试后仍然失败")


# ============================================================
# 12. 安全解析下载命令并下载字体
# ============================================================


_CURL_URL_RE = re.compile(r'''(?i)https?://[^\s"'<>|`]+''')
_CURL_OUTPUT_RE = re.compile(
    r'''(?ix)
    (?:^|\s)
    (?:--output|-o)
    \s+
    (?:"([^"]+)"|'([^']+)'|([^\s|;&]+))
    '''
)


@dataclass(frozen=True)
class FontDownloadSpec:
    url: str
    filename: str
    target_path: Path
    original_command: str


def parse_curl_command(line: str, shared_dir: Path, font_dir: Path) -> FontDownloadSpec:
    stripped = line.strip()
    if not stripped.lower().startswith("curl.exe "):
        raise ValueError(f"不是 curl.exe 命令：{line}")

    # 禁止管道、串联和 PowerShell 表达式；这里只把命令当作数据解析，不直接执行。
    forbidden = (";", "|", "&&", "||", "`", "$(", "${")
    if any(token in stripped for token in forbidden):
        raise ValueError(f"curl 命令含不允许的控制符：{line}")

    urls = _CURL_URL_RE.findall(stripped)
    urls = [url.rstrip(".,;:!?") for url in urls]
    if not urls:
        raise ValueError(f"curl 命令中没有 URL：{line}")

    # 如果命令含代理 URL，优先取不是本机代理的公网 URL。
    normalized_proxy = PROXY_URL.rstrip("/").casefold()
    url = next(
        (candidate for candidate in urls if candidate.rstrip("/").casefold() != normalized_proxy),
        urls[0],
    )

    output_match = _CURL_OUTPUT_RE.search(stripped)
    if not output_match:
        raise ValueError(f"curl 命令必须使用 -o 或 --output：{line}")
    output_value = next(value for value in output_match.groups() if value is not None)

    # 模型按 Windows PowerShell 输出反斜杠路径；显式归一化后再交给 Path。
    normalized_output_value = output_value.replace("\\", os.sep)
    output_path = Path(normalized_output_value).expanduser()
    if not output_path.is_absolute():
        output_path = (shared_dir / output_path).resolve()
    else:
        output_path = output_path.resolve()

    font_root = font_dir.resolve()
    try:
        relative = output_path.relative_to(font_root)
    except ValueError as exc:
        raise ValueError(f"字体输出必须位于 {font_root}：{output_path}") from exc

    if len(relative.parts) != 1:
        raise ValueError(f"字体必须直接保存于 resources/fonts，不得建立更深目录：{output_path}")
    if output_path.suffix.lower() not in {".otf", ".ttf", ".ttc", ".otc"}:
        raise ValueError(f"下载目标不是允许的字体扩展名：{output_path}")

    return FontDownloadSpec(
        url=url,
        filename=output_path.name,
        target_path=output_path,
        original_command=line,
    )


def parse_download_commands(
    commands_text: str,
    shared_dir: Path,
    font_dir: Path,
    create_dir: bool = True,
) -> list[FontDownloadSpec]:
    if create_dir:
        font_dir.mkdir(parents=True, exist_ok=True)
    specs_by_filename: dict[str, FontDownloadSpec] = {}

    for raw_line in commands_text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line.startswith("#") or line.upper().startswith("REM "):
            continue

        if line.lower().startswith("new-item "):
            # 目录由本程序安全创建，不执行模型给出的 PowerShell。
            continue
        if not line.lower().startswith("curl.exe "):
            raise ValueError(f"发现不允许的下载命令：{line}")

        spec = parse_curl_command(line, shared_dir, font_dir)
        key = spec.filename.casefold()
        previous = specs_by_filename.get(key)
        if previous and previous.url != spec.url:
            raise ValueError(
                f"同一个字体文件名对应多个不同 URL：{spec.filename}\n"
                f"{previous.url}\n{spec.url}"
            )
        specs_by_filename[key] = spec

    return list(specs_by_filename.values())


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def is_cjk_compatibility_ideograph(codepoint: int) -> bool:
    return (
        0xF900 <= codepoint <= 0xFAFF
        or 0x2F800 <= codepoint <= 0x2FA1F
    )


def is_cjk_unified_ideograph(codepoint: int) -> bool:
    ranges = (
        (0x3400, 0x4DBF),
        (0x4E00, 0x9FFF),
        (0x20000, 0x2A6DF),
        (0x2A700, 0x2B73F),
        (0x2B740, 0x2B81F),
        (0x2B820, 0x2CEAF),
        (0x2CEB0, 0x2EBEF),
        (0x2EBF0, 0x2EE5F),
        (0x30000, 0x3134F),
        (0x31350, 0x323AF),
    )
    return any(start <= codepoint <= end for start, end in ranges)


def scan_font_unicode_cmap(path: Path) -> dict[str, Any]:
    try:
        from fontTools import __version__ as fonttools_version
        from fontTools.ttLib import TTCollection, TTFont
    except ImportError as exc:
        raise RuntimeError(
            "缺少 fontTools，无法执行完整 Unicode cmap 扫描。"
            "请先安装：python -m pip install -U fonttools"
        ) from exc

    fonts: list[Any] = []
    collection: Any | None = None
    try:
        if path.suffix.lower() in {".ttc", ".otc"}:
            collection = TTCollection(str(path), lazy=True)
            fonts = list(collection.fonts)
        else:
            fonts = [TTFont(str(path), lazy=True)]

        ambiguous_glyphs: list[dict[str, Any]] = []
        ambiguous_standard_codepoints: set[int] = set()
        unicode_codepoints: set[int] = set()

        for face_index, font in enumerate(fonts):
            if "cmap" not in font:
                raise RuntimeError(
                    f"字体 {path.name} 的第 {face_index} 个字体面没有 cmap 表"
                )
            glyph_to_codepoints: dict[str, set[int]] = defaultdict(set)
            unicode_subtable_count = 0
            for table in font["cmap"].tables:
                try:
                    is_unicode = bool(table.isUnicode())
                except Exception:
                    is_unicode = False
                if not is_unicode:
                    continue
                unicode_subtable_count += 1
                for codepoint, glyph_name in table.cmap.items():
                    codepoint_int = int(codepoint)
                    unicode_codepoints.add(codepoint_int)
                    glyph_to_codepoints[str(glyph_name)].add(codepoint_int)

            if unicode_subtable_count <= 0:
                raise RuntimeError(
                    f"字体 {path.name} 的第 {face_index} 个字体面没有 Unicode cmap 子表"
                )

            for glyph_name, codepoints in glyph_to_codepoints.items():
                standards = sorted(
                    codepoint
                    for codepoint in codepoints
                    if is_cjk_unified_ideograph(codepoint)
                )
                compatibilities = sorted(
                    codepoint
                    for codepoint in codepoints
                    if is_cjk_compatibility_ideograph(codepoint)
                )
                if not standards or not compatibilities:
                    continue
                ambiguous_standard_codepoints.update(standards)
                ambiguous_glyphs.append(
                    {
                        "face_index": face_index,
                        "glyph_name": glyph_name,
                        "standard_codepoints": standards,
                        "compatibility_codepoints": compatibilities,
                    }
                )

        return {
            "fonttools_version": str(fonttools_version),
            "font_face_count": len(fonts),
            "unicode_codepoint_count": len(unicode_codepoints),
            "ambiguous_glyph_count": len(ambiguous_glyphs),
            "ambiguous_standard_codepoints": sorted(ambiguous_standard_codepoints),
            "ambiguous_standard_codepoint_count": len(ambiguous_standard_codepoints),
            "ambiguous_glyphs": ambiguous_glyphs,
        }
    except Exception as exc:
        if isinstance(exc, RuntimeError):
            raise
        raise RuntimeError(
            f"fontTools 无法完整扫描字体 {path.name} 的 Unicode cmap：{exc}"
        ) from exc
    finally:
        for font in fonts:
            try:
                font.close()
            except Exception:
                pass
        if collection is not None:
            try:
                collection.close()
            except Exception:
                pass


def _font_has_glyph(font: fitz.Font, char: str) -> bool:
    try:
        glyph = font.has_glyph(ord(char), fallback=False)
    except TypeError:
        glyph = font.has_glyph(ord(char))
    return bool(glyph)


def _chunk_text(text: str, chunk_size: int = FONT_ROUNDTRIP_CHUNK_SIZE) -> list[str]:
    if not text:
        return []
    return [text[index:index + chunk_size] for index in range(0, len(text), chunk_size)]


def build_font_roundtrip_test_strings(
    ambiguous_standard_codepoints: Iterable[int],
) -> list[str]:
    values: list[str] = []
    ambiguous_text = "".join(chr(codepoint) for codepoint in sorted(set(ambiguous_standard_codepoints)))
    values.extend(_chunk_text(ambiguous_text))
    values.extend(FONT_ROUNDTRIP_FIXED_TEST_STRINGS)

    unique_values: list[str] = []
    seen: set[str] = set()
    for value in values:
        if not value or value in seen:
            continue
        seen.add(value)
        unique_values.append(value)
    return unique_values


def normalize_extracted_roundtrip_text(text: str) -> str:
    value = str(text or "").replace("\r\n", "\n").replace("\r", "\n")
    if value.endswith("\n"):
        value = value[:-1]
    return value


def run_pymupdf_roundtrip_method(
    font_path: Path,
    test_strings: list[str],
    method_name: str,
) -> dict[str, Any]:
    if method_name not in {"insert_text", "insert_textbox"}:
        raise ValueError(f"未知往返测试方法：{method_name}")

    with tempfile.TemporaryDirectory(prefix="font_roundtrip_") as temp_dir_value:
        temp_dir = Path(temp_dir_value)
        output_path = temp_dir / f"{method_name}.pdf"
        doc = fitz.open()
        try:
            for index, expected_text in enumerate(test_strings):
                page = doc.new_page(width=640, height=100)
                font_alias = f"TRTEST{index + 1}"
                page.insert_font(
                    fontname=font_alias,
                    fontfile=str(font_path),
                    set_simple=False,
                )
                if method_name == "insert_text":
                    page.insert_text(
                        (20, 55),
                        expected_text,
                        fontname=font_alias,
                        fontsize=12,
                    )
                else:
                    result = page.insert_textbox(
                        fitz.Rect(20, 15, 620, 85),
                        expected_text,
                        fontname=font_alias,
                        fontsize=12,
                    )
                    if isinstance(result, (int, float)) and result < 0:
                        raise RuntimeError(
                            f"{method_name} 无法容纳测试字符串：{expected_text!r}"
                        )

            doc.subset_fonts(fallback=True)
            doc.save(str(output_path), garbage=4, deflate=True)
        finally:
            doc.close()

        if not output_path.is_file() or output_path.stat().st_size <= 0:
            raise RuntimeError(f"{method_name} 往返测试没有生成有效 PDF")

        extracted_values: list[str] = []
        with fitz.open(str(output_path)) as check_doc:
            if check_doc.page_count != len(test_strings):
                raise RuntimeError(
                    f"{method_name} 往返测试页数不一致；"
                    f"期望={len(test_strings)}，实际={check_doc.page_count}"
                )
            for page_index, expected_text in enumerate(test_strings):
                extracted_text = normalize_extracted_roundtrip_text(
                    check_doc.load_page(page_index).get_text("text")
                )
                extracted_values.append(extracted_text)
                if extracted_text != expected_text:
                    mismatch_index = 0
                    comparison_length = min(len(expected_text), len(extracted_text))
                    while (
                        mismatch_index < comparison_length
                        and expected_text[mismatch_index] == extracted_text[mismatch_index]
                    ):
                        mismatch_index += 1
                    expected_char = (
                        expected_text[mismatch_index]
                        if mismatch_index < len(expected_text)
                        else "<END>"
                    )
                    actual_char = (
                        extracted_text[mismatch_index]
                        if mismatch_index < len(extracted_text)
                        else "<END>"
                    )
                    expected_codepoint = (
                        f"U+{ord(expected_char):04X}"
                        if expected_char != "<END>"
                        else "<END>"
                    )
                    actual_codepoint = (
                        f"U+{ord(actual_char):04X}"
                        if actual_char != "<END>"
                        else "<END>"
                    )
                    raise RuntimeError(
                        f"{method_name} 精确往返失败：测试项 {page_index + 1}，"
                        f"位置 {mismatch_index}，输入={expected_char!r} {expected_codepoint}，"
                        f"提取={actual_char!r} {actual_codepoint}；"
                        f"输入全文={expected_text!r}；提取全文={extracted_text!r}"
                    )
                compatibility_characters = [
                    char
                    for char in extracted_text
                    if is_cjk_compatibility_ideograph(ord(char))
                ]
                if compatibility_characters:
                    preview = "".join(dict.fromkeys(compatibility_characters))[:40]
                    raise RuntimeError(
                        f"{method_name} 提取结果含 CJK 兼容表意文字：{preview}"
                    )

        return {
            "method": method_name,
            "exact_roundtrip": True,
            "subset_fonts_tested": True,
            "test_string_count": len(test_strings),
            "test_codepoint_count": sum(len(value) for value in test_strings),
            "compatibility_ideographs_found_after_extract": False,
        }


def validate_pymupdf_font_roundtrip(
    path: Path,
    cmap_metadata: dict[str, Any],
) -> dict[str, Any]:
    ambiguous_standard_codepoints = cmap_metadata.get("ambiguous_standard_codepoints")
    if not isinstance(ambiguous_standard_codepoints, list):
        ambiguous_standard_codepoints = []
    test_strings = build_font_roundtrip_test_strings(ambiguous_standard_codepoints)
    if not test_strings:
        raise RuntimeError(f"字体 {path.name} 的往返测试集合为空")

    try:
        font = fitz.Font(fontfile=str(path))
    except Exception as exc:
        raise RuntimeError(f"PyMuPDF 无法打开字体文件 {path.name}：{exc}") from exc

    required_characters = "".join(test_strings)
    missing_chars = [
        char
        for char in dict.fromkeys(required_characters)
        if not char.isspace() and not _font_has_glyph(font, char)
    ]
    if missing_chars:
        unique_missing = "".join(missing_chars)
        preview = unique_missing[:100]
        suffix = "…" if len(unique_missing) > 100 else ""
        raise RuntimeError(
            f"字体 {path.name} 缺少精确往返测试所需字形：{preview}{suffix}"
        )

    insert_text_result = run_pymupdf_roundtrip_method(
        path,
        test_strings,
        "insert_text",
    )
    insert_textbox_result = run_pymupdf_roundtrip_method(
        path,
        test_strings,
        "insert_textbox",
    )
    return {
        "pymupdf_version": get_pymupdf_version(),
        "test_string_count": len(test_strings),
        "test_codepoint_count": sum(len(value) for value in test_strings),
        "insert_text_exact_roundtrip": bool(insert_text_result["exact_roundtrip"]),
        "insert_textbox_exact_roundtrip": bool(insert_textbox_result["exact_roundtrip"]),
        "subset_fonts_tested": True,
        "compatibility_ideographs_found_after_extract": False,
    }


def validate_font_file(path: Path, require_chinese: bool = True) -> dict[str, Any]:
    if not path.is_file() or path.stat().st_size < MIN_FONT_FILE_SIZE:
        raise RuntimeError(f"字体文件不存在或过小：{path}")

    try:
        font = fitz.Font(fontfile=str(path))
    except Exception as exc:
        raise RuntimeError(f"PyMuPDF 无法打开字体文件 {path.name}：{exc}") from exc

    missing_chars: list[str] = []
    if require_chinese:
        for char in FONT_GLYPH_TEST_TEXT:
            if not _font_has_glyph(font, char):
                missing_chars.append(char)

    if missing_chars:
        unique_missing = "".join(dict.fromkeys(missing_chars))
        raise RuntimeError(
            f"字体 {path.name} 缺少测试中文字形：{unique_missing}"
        )

    cmap_metadata = scan_font_unicode_cmap(path)
    roundtrip_metadata = validate_pymupdf_font_roundtrip(path, cmap_metadata)

    return {
        "file_name": path.name,
        "size_bytes": path.stat().st_size,
        "sha256": sha256_file(path),
        "font_name": getattr(font, "name", ""),
        "glyph_count": int(getattr(font, "glyph_count", 0) or 0),
        "is_bold": bool(getattr(font, "is_bold", False)),
        "is_italic": bool(getattr(font, "is_italic", False)),
        "is_serif": bool(getattr(font, "is_serif", False)),
        "is_monospaced": bool(getattr(font, "is_monospaced", False)),
        "fonttools_version": cmap_metadata["fonttools_version"],
        "font_face_count": cmap_metadata["font_face_count"],
        "unicode_codepoint_count": cmap_metadata["unicode_codepoint_count"],
        "ambiguous_glyph_count": cmap_metadata["ambiguous_glyph_count"],
        "ambiguous_standard_codepoint_count": cmap_metadata[
            "ambiguous_standard_codepoint_count"
        ],
        "ambiguous_standard_codepoints": cmap_metadata[
            "ambiguous_standard_codepoints"
        ],
        "pymupdf_version": roundtrip_metadata["pymupdf_version"],
        "roundtrip_test_string_count": roundtrip_metadata["test_string_count"],
        "roundtrip_test_codepoint_count": roundtrip_metadata[
            "test_codepoint_count"
        ],
        "insert_text_exact_roundtrip": roundtrip_metadata[
            "insert_text_exact_roundtrip"
        ],
        "insert_textbox_exact_roundtrip": roundtrip_metadata[
            "insert_textbox_exact_roundtrip"
        ],
        "subset_fonts_tested": roundtrip_metadata["subset_fonts_tested"],
        "compatibility_ideographs_found_after_extract": roundtrip_metadata[
            "compatibility_ideographs_found_after_extract"
        ],
        "font_validation_version": FONT_VALIDATION_VERSION,
    }


def download_one_font(spec: FontDownloadSpec, force: bool) -> dict[str, Any]:
    target = spec.target_path
    target.parent.mkdir(parents=True, exist_ok=True)

    if target.is_file() and target.stat().st_size >= MIN_FONT_FILE_SIZE and not force:
        try:
            metadata = validate_font_file(target, require_chinese=True)
            print(f"  ✓ 字体已存在并通过完整验证：{target.name}")
            return metadata
        except Exception as exc:
            print(f"  ⚠ 现有字体验证失败，将重新下载：{target.name}：{exc}")

    temp = target.with_name(
        f"{target.name}.{os.getpid()}.{threading.get_ident()}.downloading"
    )
    temp.unlink(missing_ok=True)

    print(f"  🌐 下载字体：{spec.filename}")
    print(f"     {spec.url}")

    session = build_session()
    try:
        response = session.get(
            spec.url,
            headers={"User-Agent": "Mozilla/5.0", "Cache-Control": "no-cache"},
            timeout=REQUEST_TIMEOUT,
            stream=True,
            allow_redirects=True,
        )
        if response.status_code != 200:
            raise RuntimeError(f"HTTP {response.status_code}：{response.text[:500]}")

        content_type = str(response.headers.get("Content-Type") or "").casefold()
        if "text/html" in content_type:
            raise RuntimeError(
                f"字体下载返回 HTML，Content-Type={response.headers.get('Content-Type')}"
            )

        with temp.open("wb") as handle:
            for chunk in response.iter_content(chunk_size=1024 * 1024):
                if chunk:
                    handle.write(chunk)

        temp_metadata = validate_font_file(temp, require_chinese=True)
        os.replace(temp, target)
        final_metadata = validate_font_file(target, require_chinese=True)
        if temp_metadata["sha256"] != final_metadata["sha256"]:
            raise RuntimeError(f"字体原子替换后 SHA256 发生变化：{target.name}")
        print(f"  ✓ 字体下载并完成 cmap 与 PyMuPDF 精确往返验证：{target}")
        return final_metadata
    finally:
        session.close()
        temp.unlink(missing_ok=True)


def rebind_font_download_specs(
    specs: list[FontDownloadSpec],
    target_font_dir: Path,
) -> list[FontDownloadSpec]:
    """在已完成生产路径安全校验后，把下载目标改绑到副本私有字体目录。"""
    target_font_dir.mkdir(parents=True, exist_ok=True)
    target_root = target_font_dir.resolve()
    rebound: list[FontDownloadSpec] = []
    for spec in specs:
        target_path = (target_root / spec.filename).resolve()
        try:
            relative = target_path.relative_to(target_root)
        except ValueError as exc:
            raise ValueError(f"副本字体目标越界：{target_path}") from exc
        if len(relative.parts) != 1:
            raise ValueError(f"副本字体目标不是直接子文件：{target_path}")
        rebound.append(
            FontDownloadSpec(
                url=spec.url,
                filename=spec.filename,
                target_path=target_path,
                original_command=spec.original_command,
            )
        )
    return rebound


def ensure_mapping_fonts(
    mappings: dict[str, FontMappingDecision | None],
    commands_text: str,
    output_root: Path,
    force_download: bool,
    target_font_dir: Path | None = None,
) -> dict[str, dict[str, Any]]:
    shared_dir = get_shared_dir(output_root)
    font_dir = get_font_dir(output_root)
    shared_dir.mkdir(parents=True, exist_ok=True)
    if target_font_dir is None:
        font_dir.mkdir(parents=True, exist_ok=True)

    specs = parse_download_commands(
        commands_text,
        shared_dir,
        font_dir,
        create_dir=target_font_dir is None,
    )
    if target_font_dir is not None:
        specs = rebind_font_download_specs(specs, target_font_dir)
    specs_by_name = {spec.filename.casefold(): spec for spec in specs}

    required_by_filename: dict[str, str] = {}
    for decision in mappings.values():
        if decision is None:
            continue

        filename_key = decision.target_font_file.casefold()
        previous_url = required_by_filename.get(filename_key)
        if previous_url is not None and previous_url != decision.download_url:
            raise ValueError(
                f"多个原字体把同一个目标文件名映射到不同 URL：{decision.target_font_file}\n"
                f"{previous_url}\n{decision.download_url}"
            )
        required_by_filename[filename_key] = decision.download_url

    missing_commands: list[str] = []
    mismatched_urls: list[str] = []
    for filename_key, expected_url in sorted(required_by_filename.items()):
        spec = specs_by_name.get(filename_key)
        if spec is None:
            missing_commands.append(filename_key)
            continue
        if spec.url != expected_url:
            mismatched_urls.append(
                f"{spec.filename}: JSON={expected_url}；curl={spec.url}"
            )

    if missing_commands:
        raise ValueError(
            f"以下映射字体没有对应 curl 下载命令：{missing_commands}"
        )
    if mismatched_urls:
        raise ValueError(
            "字体映射 JSON 的 download_url 与 curl 命令不一致：\n"
            + "\n".join(mismatched_urls)
        )

    # 只下载映射实际引用的文件；忽略模型多给出的未引用字体。
    metadata: dict[str, dict[str, Any]] = {}
    for filename_key in sorted(required_by_filename):
        spec = specs_by_name[filename_key]
        try:
            file_metadata = download_one_font(spec, force=force_download)
        except Exception as exc:
            existing_sha256 = ""
            if spec.target_path.is_file() and spec.target_path.stat().st_size > 0:
                try:
                    existing_sha256 = sha256_file(spec.target_path)
                except Exception:
                    existing_sha256 = ""
            raise FontCandidateValidationError(
                target_font_file=spec.filename,
                download_url=spec.url,
                sha256=existing_sha256,
                reason=f"{type(exc).__name__}: {exc}",
            ) from exc
        file_metadata["download_url"] = required_by_filename[filename_key]
        metadata[spec.filename] = file_metadata

    return metadata


def promote_mapping_race_fonts(
    result: MappingRaceCopyResult,
    output_root: Path,
) -> None:
    """将获胜副本已验证的字体逐个原子晋升到公共 fonts 目录。"""
    public_font_dir = get_font_dir(output_root)
    public_font_dir.mkdir(parents=True, exist_ok=True)
    source_root = result.font_dir.resolve()

    # 先完成整批只读预检，避免某个字体冲突时前面的字体已经部分晋升。
    for filename, expected_metadata in sorted(result.local_metadata.items()):
        source_path = (source_root / filename).resolve()
        try:
            source_relative = source_path.relative_to(source_root)
        except ValueError as exc:
            raise FontCandidateValidationError(
                filename,
                str(expected_metadata.get("download_url") or ""),
                f"获胜副本字体路径越界：{source_path}",
            ) from exc
        if len(source_relative.parts) != 1 or not source_path.is_file():
            raise FontCandidateValidationError(
                filename,
                str(expected_metadata.get("download_url") or ""),
                f"获胜副本缺少已验证字体：{source_path}",
            )
        source_metadata = validate_font_file(source_path, require_chinese=True)
        source_sha256 = str(source_metadata.get("sha256") or "").lower()
        expected_sha256 = str(expected_metadata.get("sha256") or "").lower()
        download_url = str(expected_metadata.get("download_url") or "")
        if not source_sha256 or source_sha256 != expected_sha256:
            raise FontCandidateValidationError(
                filename,
                download_url,
                "获胜副本字体在晋升前的 SHA256 与验证记录不一致",
                source_sha256,
            )
        target_path = (public_font_dir / filename).resolve()
        try:
            target_relative = target_path.relative_to(public_font_dir.resolve())
        except ValueError as exc:
            raise FontCandidateValidationError(
                filename,
                download_url,
                f"公共字体目标越界：{target_path}",
                source_sha256,
            ) from exc
        if len(target_relative.parts) != 1:
            raise FontCandidateValidationError(
                filename,
                download_url,
                f"公共字体目标不是直接子文件：{target_path}",
                source_sha256,
            )
        if target_path.is_file():
            existing_metadata = validate_font_file(target_path, require_chinese=True)
            existing_sha256 = str(existing_metadata.get("sha256") or "").lower()
            if existing_sha256 != source_sha256:
                raise FontCandidateValidationError(
                    filename,
                    download_url,
                    "公共字体目录中已存在同名但 SHA256 不同的字体",
                    source_sha256,
                )

    for filename, expected_metadata in sorted(result.local_metadata.items()):
        source_path = (source_root / filename).resolve()
        try:
            source_relative = source_path.relative_to(source_root)
        except ValueError as exc:
            raise FontCandidateValidationError(
                filename,
                str(expected_metadata.get("download_url") or ""),
                f"获胜副本字体路径越界：{source_path}",
            ) from exc
        if len(source_relative.parts) != 1 or not source_path.is_file():
            raise FontCandidateValidationError(
                filename,
                str(expected_metadata.get("download_url") or ""),
                f"获胜副本缺少已验证字体：{source_path}",
            )

        source_metadata = validate_font_file(source_path, require_chinese=True)
        source_sha256 = str(source_metadata.get("sha256") or "").lower()
        expected_sha256 = str(expected_metadata.get("sha256") or "").lower()
        download_url = str(expected_metadata.get("download_url") or "")
        if not source_sha256 or source_sha256 != expected_sha256:
            raise FontCandidateValidationError(
                filename,
                download_url,
                "获胜副本字体在晋升前的 SHA256 与验证记录不一致",
                source_sha256,
            )

        target_path = (public_font_dir / filename).resolve()
        try:
            target_relative = target_path.relative_to(public_font_dir.resolve())
        except ValueError as exc:
            raise FontCandidateValidationError(
                filename,
                download_url,
                f"公共字体目标越界：{target_path}",
                source_sha256,
            ) from exc
        if len(target_relative.parts) != 1:
            raise FontCandidateValidationError(
                filename,
                download_url,
                f"公共字体目标不是直接子文件：{target_path}",
                source_sha256,
            )

        if target_path.is_file():
            existing_metadata = validate_font_file(target_path, require_chinese=True)
            existing_sha256 = str(existing_metadata.get("sha256") or "").lower()
            if existing_sha256 != source_sha256:
                raise FontCandidateValidationError(
                    filename,
                    download_url,
                    "公共字体目录中已存在同名但 SHA256 不同的字体",
                    source_sha256,
                )
            print(f"  ✓ 竞速获胜副本字体已在公共目录中：{filename}")
            continue

        publishing_path = target_path.with_name(
            f"{target_path.name}.{result.copy_id}.{os.getpid()}.publishing"
        )
        publishing_path.unlink(missing_ok=True)
        try:
            shutil.copy2(source_path, publishing_path)
            published_metadata = validate_font_file(
                publishing_path,
                require_chinese=True,
            )
            published_sha256 = str(published_metadata.get("sha256") or "").lower()
            if published_sha256 != source_sha256:
                raise FontCandidateValidationError(
                    filename,
                    download_url,
                    "字体晋升临时文件 SHA256 不一致",
                    published_sha256,
                )
            os.replace(publishing_path, target_path)
        finally:
            publishing_path.unlink(missing_ok=True)

        final_metadata = validate_font_file(target_path, require_chinese=True)
        final_sha256 = str(final_metadata.get("sha256") or "").lower()
        if final_sha256 != source_sha256:
            raise FontCandidateValidationError(
                filename,
                download_url,
                "字体原子晋升后 SHA256 不一致",
                final_sha256,
            )
        print(f"  🏁 竞速获胜副本字体已原子晋升：{filename}")


def validate_model_report_against_local_fonts(
    validation_report: dict[str, Any],
    local_metadata: dict[str, dict[str, Any]],
) -> None:
    report_fonts = validation_report.get("fonts")
    if not isinstance(report_fonts, dict):
        raise ValueError("模型字体校验报告 fonts 不是对象")
    report_by_normalized = {
        str(filename).casefold(): (str(filename), report)
        for filename, report in report_fonts.items()
    }
    local_by_normalized = {
        filename.casefold(): (filename, metadata)
        for filename, metadata in local_metadata.items()
    }
    if set(report_by_normalized) != set(local_by_normalized):
        raise ValueError(
            "模型校验报告与本地实际验证的字体集合不一致；"
            f"模型={sorted(report_by_normalized)}；本地={sorted(local_by_normalized)}"
        )

    for normalized_name in sorted(local_by_normalized):
        local_name, metadata = local_by_normalized[normalized_name]
        report_name, report = report_by_normalized[normalized_name]
        if not isinstance(report, dict):
            raise ValueError(f"模型字体校验项不是对象：{report_name}")
        expected_url = str(metadata.get("download_url") or "")
        local_sha256 = str(metadata.get("sha256") or "").lower()
        local_size = int(metadata.get("size_bytes") or 0)
        report_url = str(report.get("download_url") or "")
        report_sha256 = str(report.get("sha256") or "").lower()
        report_size = int(report.get("size_bytes") or 0)
        if (
            report_url != expected_url
            or report_sha256 != local_sha256
            or report_size != local_size
        ):
            raise FontCandidateValidationError(
                target_font_file=local_name,
                download_url=expected_url,
                sha256=local_sha256,
                reason=(
                    "模型本地校验报告与生产环境下载到的实际字体资源不一致；"
                    f"模型 URL={report_url}，本地 URL={expected_url}；"
                    f"模型 SHA256={report_sha256}，本地 SHA256={local_sha256}；"
                    f"模型大小={report_size}，本地大小={local_size}"
                ),
            )
        if metadata.get("insert_text_exact_roundtrip") is not True:
            raise FontCandidateValidationError(
                local_name,
                expected_url,
                "生产环境 insert_text 精确往返测试未通过",
                local_sha256,
            )
        if metadata.get("insert_textbox_exact_roundtrip") is not True:
            raise FontCandidateValidationError(
                local_name,
                expected_url,
                "生产环境 insert_textbox 精确往返测试未通过",
                local_sha256,
            )
        if metadata.get("compatibility_ideographs_found_after_extract") is not False:
            raise FontCandidateValidationError(
                local_name,
                expected_url,
                "生产环境提取结果含 CJK 兼容表意文字",
                local_sha256,
            )


def validate_mapping_against_rejected_fonts(
    mappings: dict[str, FontMappingDecision | None],
    validation_report: dict[str, Any],
    rejected_candidates: list[RejectedFontCandidate],
) -> None:
    rejected_filenames = {
        item.target_font_file.casefold()
        for item in rejected_candidates
        if item.target_font_file
    }
    rejected_urls = {
        item.download_url
        for item in rejected_candidates
        if item.download_url
    }
    rejected_sha256 = {
        item.sha256.lower()
        for item in rejected_candidates
        if item.sha256
    }
    report_fonts = validation_report.get("fonts")
    report_by_normalized = (
        {
            str(filename).casefold(): report
            for filename, report in report_fonts.items()
            if isinstance(filename, str) and isinstance(report, dict)
        }
        if isinstance(report_fonts, dict)
        else {}
    )

    for decision in mappings.values():
        if decision is None:
            continue
        normalized_filename = decision.target_font_file.casefold()
        report = report_by_normalized.get(normalized_filename, {})
        reported_sha256 = str(report.get("sha256") or "").lower()
        if normalized_filename in rejected_filenames:
            raise RejectedFontReuseError(
                f"模型再次返回了已失败的字体文件名：{decision.target_font_file}"
            )
        if decision.download_url in rejected_urls:
            raise RejectedFontReuseError(
                f"模型再次返回了已失败的字体 URL：{decision.download_url}"
            )
        if reported_sha256 and reported_sha256 in rejected_sha256:
            raise RejectedFontReuseError(
                f"模型再次返回了已失败字体的 SHA256：{reported_sha256}"
            )


def run_mapping_race_copy(
    base_prompt: str,
    expected_keys: set[str],
    output_root: Path,
    round_num: int,
    validation_cycle: int,
    copy_id: str,
    race_copy_count: int,
    rejected_candidates: list[RejectedFontCandidate],
    allow_validated_resume: bool,
    force_download: bool,
    skip_download: bool,
    stop_event: threading.Event,
) -> MappingRaceCopyResult:
    """执行一个完全隔离的映射副本；本函数绝不向公共字体目录写入。"""
    copy_work_dir = get_mapping_race_copy_dir(
        get_shared_dir(output_root) / FONT_STAGE_WORK_DIR_NAME,
        round_num,
        validation_cycle,
        copy_id,
    )
    copy_font_dir = get_mapping_race_font_dir(copy_work_dir)
    copy_work_dir.mkdir(parents=True, exist_ok=True)
    copy_font_dir.mkdir(parents=True, exist_ok=True)
    copy_label = f"{copy_id} / 第 {round_num} 轮"
    prompt = render_prompt_with_rejected_fonts(base_prompt, rejected_candidates)

    (copy_work_dir / "00_race_copy_info.json").write_text(
        json.dumps(
            {
                "copy_id": copy_id,
                "round_num": round_num,
                "validation_cycle": validation_cycle,
                "race_copy_count": race_copy_count,
                "font_dir": str(copy_font_dir),
                "started_at": time.strftime("%Y-%m-%d %H:%M:%S"),
            },
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )

    try:
        if stop_event.is_set():
            return MappingRaceCopyResult(
                copy_id=copy_id,
                work_dir=copy_work_dir,
                font_dir=copy_font_dir,
                success=False,
                error_message="其他竞速副本已获胜，当前副本未发起请求",
            )

        (
            commands_text,
            decisions,
            validation_report,
            validated_raw,
        ) = request_mapping_round(
            prompt=prompt,
            expected_keys=expected_keys,
            work_dir=copy_work_dir,
            round_num=round_num,
            task_label=f"请求字体映射竞速副本 {copy_label}",
            allow_validated_resume=allow_validated_resume,
            max_attempts=1,
        )
        if stop_event.is_set():
            return MappingRaceCopyResult(
                copy_id=copy_id,
                work_dir=copy_work_dir,
                font_dir=copy_font_dir,
                success=False,
                error_message="其他竞速副本已获胜，当前副本不再验证或发布",
            )

        validate_mapping_against_rejected_fonts(
            decisions,
            validation_report,
            rejected_candidates,
        )

        local_metadata: dict[str, dict[str, Any]] = {}
        if not skip_download:
            local_metadata = ensure_mapping_fonts(
                mappings=decisions,
                commands_text=commands_text,
                output_root=output_root,
                force_download=force_download,
                target_font_dir=copy_font_dir,
            )
            validate_model_report_against_local_fonts(
                validation_report,
                local_metadata,
            )
            (copy_work_dir / f"01_round_{round_num:03d}_local_font_validation.json").write_text(
                json.dumps(local_metadata, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
            print(
                f"  ✓ {copy_label} 候选字体已在副本私有目录通过 "
                "fontTools cmap 扫描和 PyMuPDF 精确往返验证"
            )

        if stop_event.is_set():
            return MappingRaceCopyResult(
                copy_id=copy_id,
                work_dir=copy_work_dir,
                font_dir=copy_font_dir,
                success=False,
                error_message="其他竞速副本已获胜，当前副本验证结果仅保留在私有目录",
            )

        return MappingRaceCopyResult(
            copy_id=copy_id,
            work_dir=copy_work_dir,
            font_dir=copy_font_dir,
            success=True,
            commands_text=commands_text,
            decisions=decisions,
            validation_report=validation_report,
            validated_raw=validated_raw,
            local_metadata=local_metadata,
        )

    except FontCandidateValidationError as exc:
        rejected = record_rejected_font_candidate(
            work_dir=copy_work_dir,
            target_font_file=exc.target_font_file,
            download_url=exc.download_url,
            sha256=exc.sha256,
            reason=exc.reason,
        )
        return MappingRaceCopyResult(
            copy_id=copy_id,
            work_dir=copy_work_dir,
            font_dir=copy_font_dir,
            success=False,
            rejected_candidate=rejected,
            error_message=(
                f"候选字体验证失败：{rejected.target_font_file or '未知'}；"
                f"{rejected.reason}"
            ),
        )
    except Exception as exc:
        return MappingRaceCopyResult(
            copy_id=copy_id,
            work_dir=copy_work_dir,
            font_dir=copy_font_dir,
            success=False,
            error_message=f"{type(exc).__name__}: {exc}",
        )


def save_mapping_race_winner(
    work_dir: Path,
    round_num: int,
    validation_cycle: int,
    result: MappingRaceCopyResult,
) -> None:
    """记录本轮获胜者；此文件由单一调度线程写入。"""
    path = work_dir / f"01_round_{round_num:03d}_race_winner.json"
    payload = {
        "round_num": round_num,
        "validation_cycle": validation_cycle,
        "winner_copy_id": result.copy_id,
        "winner_work_dir": str(result.work_dir),
        "winner_font_dir": str(result.font_dir),
        "completed_at": time.strftime("%Y-%m-%d %H:%M:%S"),
    }
    temp_path = path.with_name(f"{path.name}.{os.getpid()}.tmp")
    temp_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    os.replace(temp_path, path)


def request_locally_validated_mapping_round(
    base_prompt: str,
    expected_keys: set[str],
    work_dir: Path,
    output_root: Path,
    round_num: int,
    task_label: str,
    allow_validated_resume: bool,
    force_download: bool,
    skip_download: bool,
    race_copies: int,
) -> tuple[
    str,
    dict[str, FontMappingDecision | None],
    dict[str, Any],
    str,
]:
    if race_copies < 1:
        raise ValueError("竞速副本数量必须至少为 1")

    for validation_cycle in range(1, RETRY_COUNT + 1):
        rejected_candidates = load_rejected_font_candidates(work_dir)
        if validation_cycle > 1:
            print(
                f"{task_label}进入第 {validation_cycle} 次候选字体重选；"
                f"当前失败字体黑名单数量：{len(rejected_candidates)}"
            )
        print(
            f"\n=== {task_label}：第 {validation_cycle} 次候选字体竞速；"
            f"并发副本数 {race_copies} ==="
        )

        stop_event = threading.Event()
        executor = ThreadPoolExecutor(
            max_workers=race_copies,
            thread_name_prefix=f"font-map-r{round_num:03d}",
        )
        futures: set[Future[MappingRaceCopyResult]] = set()
        winner: MappingRaceCopyResult | None = None
        rejected_failures: list[RejectedFontCandidate] = []
        try:
            for copy_index in range(race_copies):
                copy_id = f"copy_{copy_index:03d}"
                future = executor.submit(
                    run_mapping_race_copy,
                    base_prompt,
                    expected_keys,
                    output_root,
                    round_num,
                    validation_cycle,
                    copy_id,
                    race_copies,
                    rejected_candidates,
                    allow_validated_resume and validation_cycle == 1,
                    force_download,
                    skip_download,
                    stop_event,
                )
                futures.add(future)
                print(f"  🚀 已启动字体映射竞速副本：{copy_id}")

            while futures:
                done_futures, futures = wait(
                    futures,
                    return_when=FIRST_COMPLETED,
                )
                for future in done_futures:
                    try:
                        result = future.result()
                    except Exception as exc:
                        print(f"  ✗ 竞速副本线程未捕获异常：{type(exc).__name__}: {exc}")
                        continue

                    if not result.success:
                        print(
                            f"  ↻ 竞速副本 {result.copy_id} 未获有效结果："
                            f"{result.error_message or '未知原因'}"
                        )
                        if result.rejected_candidate is not None:
                            rejected_failures.append(result.rejected_candidate)
                        continue

                    try:
                        if not skip_download:
                            promote_mapping_race_fonts(result, output_root)
                    except FontCandidateValidationError as exc:
                        rejected_failures.append(
                            record_rejected_font_candidate(
                                work_dir=result.work_dir,
                                target_font_file=exc.target_font_file,
                                download_url=exc.download_url,
                                sha256=exc.sha256,
                                reason=exc.reason,
                            )
                        )
                        print(
                            f"  ↻ 竞速副本 {result.copy_id} 的资源晋升失败，"
                            "继续等待其他副本："
                            f"{exc}"
                        )
                        continue

                    winner = result
                    stop_event.set()
                    print(
                        f"  🏁 第 {round_num} 轮竞速获胜副本：{winner.copy_id}；"
                        "其余副本仅保留私有证据，不得发布到公共目录"
                    )
                    save_mapping_race_winner(
                        work_dir,
                        round_num,
                        validation_cycle,
                        winner,
                    )
                    return (
                        winner.commands_text,
                        winner.decisions,
                        winner.validation_report,
                        winner.validated_raw,
                    )
        finally:
            if winner is not None:
                stop_event.set()
                for future in futures:
                    future.cancel()
                # 已启动的请求只会继续写入自己的副本目录；不等待它们，避免赢家
                # 被慢副本拖住。阶段 0 的公共资源只由上方调度线程晋升。
                executor.shutdown(wait=False, cancel_futures=True)
            else:
                executor.shutdown(wait=True, cancel_futures=False)

        if rejected_failures:
            for failed_candidate in rejected_failures:
                record_rejected_font_candidate(
                    work_dir=work_dir,
                    target_font_file=failed_candidate.target_font_file,
                    download_url=failed_candidate.download_url,
                    sha256=failed_candidate.sha256,
                    reason=failed_candidate.reason,
                )
            rejected_total = load_rejected_font_candidates(work_dir)
            print(
                "↻ 本次全部竞速副本均未获有效结果；已将失败候选合并进主黑名单：\n"
                f"  本次失败候选数：{len(rejected_failures)}；"
                f"当前主黑名单总数：{len(rejected_total)}"
            )
        else:
            print("↻ 本次全部竞速副本均未获有效映射，将使用同一黑名单重新发起竞速")

    raise RuntimeError(
        f"{task_label}在 {RETRY_COUNT} 次候选字体竞速后仍未得到可用结果"
    )


# ============================================================
# 13. 保存最终映射
# ============================================================


def save_final_mapping(
    output_root: Path,
    pdf_path: Path,
    selected_pages: list[int],
    mappings: dict[str, FontMappingDecision | None],
    font_metadata: dict[str, dict[str, Any]],
    commands_text: str,
    validated_responses: list[str],
    validation_reports: list[dict[str, Any]],
    rejected_candidates: list[RejectedFontCandidate],
    local_validation_completed: bool,
    work_dir: Path,
) -> None:
    shared_dir = get_shared_dir(output_root)
    shared_dir.mkdir(parents=True, exist_ok=True)

    final_mappings: dict[str, dict[str, Any] | None] = {}
    for key in sorted(mappings, key=lambda value: value.casefold()):
        decision = mappings[key]
        if decision is None:
            final_mappings[key] = None
            continue

        metadata = font_metadata.get(decision.target_font_file, {})
        final_mappings[key] = {
            "target_font_file": decision.target_font_file,
            "download_url": decision.download_url,
            "sha256": metadata.get("sha256"),
            "size_bytes": metadata.get("size_bytes"),
        }

    mapping_payload = {
        "version": 3,
        "font_validation_version": (
            FONT_VALIDATION_VERSION if local_validation_completed else 0
        ),
        "mappings": final_mappings,
    }

    mapping_path = get_mapping_path(output_root)
    temp_mapping = mapping_path.with_name(mapping_path.name + ".tmp")
    temp_mapping.write_text(
        json.dumps(mapping_payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    os.replace(temp_mapping, mapping_path)

    meta_payload = {
        "version": 3,
        "font_validation_version": (
            FONT_VALIDATION_VERSION if local_validation_completed else 0
        ),
        "local_validation_completed": local_validation_completed,
        "pymupdf_version": get_pymupdf_version(),
        "python_version": sys.version,
        "generated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "source_pdf": str(pdf_path),
        "source_pdf_sha256": sha256_file(pdf_path),
        "selected_pages": sorted(set(selected_pages)),
        "font_files": font_metadata,
        "model_font_validation_reports": validation_reports,
        "rejected_font_candidates": [
            {
                "target_font_file": item.target_font_file,
                "download_url": item.download_url,
                "sha256": item.sha256,
                "reason": item.reason,
                "rejected_at": item.rejected_at,
            }
            for item in rejected_candidates
        ],
    }
    meta_path = shared_dir / FONT_MAPPING_META_FILE_NAME
    temp_meta = meta_path.with_name(meta_path.name + ".tmp")
    temp_meta.write_text(
        json.dumps(meta_payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    os.replace(temp_meta, meta_path)

    (work_dir / "01_font_download_commands.txt").write_text(commands_text, encoding="utf-8")
    (work_dir / "01_model_response_validated.txt").write_text(
        "\n\n".join(
            f"===== ROUND {index:03d} =====\n{response}"
            for index, response in enumerate(validated_responses, start=1)
        ),
        encoding="utf-8",
    )
    (work_dir / MODEL_FONT_VALIDATION_REPORTS_FILE_NAME).write_text(
        json.dumps(
            {
                "version": 1,
                "reports": validation_reports,
            },
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )
    (work_dir / "FONT_MAPPING_COMPLETED").write_text(
        time.strftime("%Y-%m-%d %H:%M:%S"),
        encoding="utf-8",
    )

    print(f"✓ 最终字体映射：{mapping_path}")
    print(f"✓ 字体资源目录：{get_font_dir(output_root)}")
    print(f"✓ 映射元数据：{meta_path}")


# ============================================================
# 14. 主流程
# ============================================================


def main() -> None:
    parser = argparse.ArgumentParser(
        description="阶段 0：提取 PDF 字体、选择代表页并生成全书统一中文字体映射。"
    )
    parser.add_argument(
        "--transcribe-script",
        default=TRANSCRIBE_SCRIPT_NAME,
        help="转录脚本路径；默认读取本脚本同目录下的转录脚本。",
    )
    parser.add_argument("--pdf", default=None, help="显式指定 PDF；默认读取转录脚本 PDF_INPUT。")
    parser.add_argument("--output-root", default=None, help="精翻工程输出目录。")
    parser.add_argument("--force", action="store_true", help="强制重新分析、重新请求模型并覆盖映射。")
    parser.add_argument("--skip-upload", action="store_true", help="跳过代表单页 PDF 的 GitHub 上传。")
    parser.add_argument("--skip-download", action="store_true", help="只生成映射，不下载字体；主要用于调试。")
    parser.add_argument(
        "--race-copies",
        type=int,
        default=MAPPING_RACE_COPY_COUNT,
        help=(
            "每轮字体映射同时启动的独立竞速副本数；默认 "
            f"{MAPPING_RACE_COPY_COUNT}，至少为 1。"
        ),
    )
    args = parser.parse_args()

    if args.race_copies < 1:
        parser.error("--race-copies 必须至少为 1")

    if not BASE_URL:
        raise RuntimeError("未配置环境变量 EASYGPT_URL")
    if not MODEL:
        raise RuntimeError("未配置环境变量 EASYGPT_MODEL")
    if not API_KEYS:
        raise RuntimeError("未配置 EASYGPT_KEY1～EASYGPT_KEY8 中的任何一个 Key")

    transcribe_script, pdf_path, output_root, work_dir = resolve_runtime_config(args)
    output_root.mkdir(parents=True, exist_ok=True)
    work_dir.mkdir(parents=True, exist_ok=True)
    get_font_dir(output_root).mkdir(parents=True, exist_ok=True)

    mapping_path = get_mapping_path(output_root)
    if (
        SKIP_WHEN_MAPPING_EXISTS
        and mapping_file_is_current(mapping_path)
        and not args.force
    ):
        print(f"✓ 当前版本字体映射已存在，跳过：{mapping_path}")
        print(mapping_path.read_text(encoding="utf-8-sig"))
        return
    if mapping_path.is_file() and not mapping_file_is_current(mapping_path) and not args.force:
        print(f"⚠ 检测到旧版或无效字体映射，将自动重新生成：{mapping_path}")

    github_repo_url = (
        read_literal_assignment(transcribe_script, "GITHUB_REPO_URL")
        or "https://github.com/a2848273598/pdf-transcribe-images.git"
    )
    github_branch = read_literal_assignment(transcribe_script, "GITHUB_BRANCH") or "main"
    github_push_retry = int(read_literal_assignment(transcribe_script, "GITHUB_PUSH_RETRY", 3) or 3)

    print("=" * 72)
    print("=== 数据手册精翻：阶段 0 字体提取与全局映射 ===")
    print("=" * 72)
    print(f"转录脚本：{transcribe_script}")
    print(f"PDF：{pdf_path}")
    print(f"工程目录：{output_root}")
    print(f"公共资源目录：{get_shared_dir(output_root)}")
    print(f"字体目录：{get_font_dir(output_root)}")
    print(f"工作目录：{work_dir}")
    print(f"模型：{MODEL}")
    print(f"API Key 数：{len(API_KEYS)}")
    print(f"每轮字体映射竞速副本数：{args.race_copies}")
    print(
        "竞速副本资源策略：每个副本独立保存请求、报告和候选字体；"
        "仅完整校验获胜者可原子晋升到公共字体目录"
    )
    print(f"GitHub 仓库：{github_repo_url}")
    print(f"GitHub 分支：{github_branch}")
    print(f"生产环境 PyMuPDF 版本：{get_pymupdf_version()}")
    print(
        f"流式详细日志：每 {STREAM_PROGRESS_PRINT_INTERVAL_SECONDS:g} 秒；"
        f"首数据超时 {STREAM_FIRST_DATA_TIMEOUT_SECONDS:g} 秒；"
        f"空闲超时 {STREAM_IDLE_TIMEOUT_SECONDS:g} 秒；"
        f"绝对超时 {STREAM_ABSOLUTE_TIMEOUT_SECONDS:g} 秒"
    )
    print(
        f"异步报告断点续传：{'开启' if ASYNC_REPORT_RESUME_ENABLED else '关闭'}；"
        f"轮询间隔 {ASYNC_REPORT_POLL_INTERVAL_SECONDS:g} 秒；"
        f"总等待上限 {ASYNC_REPORT_PROCESSING_TIMEOUT_SECONDS:g} 秒"
    )
    print(
        "字体安全校验：模型工具环境完整 cmap + PyMuPDF 精确往返；"
        "生产环境再次执行相同原则的完整校验"
    )

    font_records, page_stats = extract_font_inventory(pdf_path)
    selected_pages = select_representative_pages(font_records, page_stats)
    selected_page_set = set(selected_pages)

    pages_dir = pdf_path.parent / PDF_PAGES_DIR_NAME
    split_selected_pages(
        pdf_path=pdf_path,
        pages_dir=pages_dir,
        selected_pages=selected_pages,
        force=args.force,
    )

    github_folder = get_github_folder_name(pdf_path)
    if not args.skip_upload:
        upload_selected_pages_to_github(
            pages_dir=pages_dir,
            selected_pages=selected_pages,
            folder_name=github_folder,
            repo_url=github_repo_url,
            branch=github_branch,
            push_retry=github_push_retry,
        )
    else:
        print("已按 --skip-upload 跳过 GitHub 上传；提示词仍将使用预计的 raw URL。")

    prompt = build_prompt(
        font_records=font_records,
        selected_pages=selected_pages,
        page_stats=page_stats,
        repo_url=github_repo_url,
        branch=github_branch,
        folder_name=github_folder,
    )

    write_inventory_files(
        work_dir=work_dir,
        pdf_path=pdf_path,
        font_records=font_records,
        page_stats=page_stats,
        selected_pages=selected_pages,
        prompt=prompt,
    )

    all_commands: list[str] = []
    validated_responses: list[str] = []
    validation_reports: list[dict[str, Any]] = []
    final_decisions: dict[str, FontMappingDecision | None] = {}

    (
        commands_text,
        round_decisions,
        validation_report,
        validated_raw,
    ) = request_locally_validated_mapping_round(
        base_prompt=prompt,
        expected_keys=set(font_records),
        work_dir=work_dir,
        output_root=output_root,
        round_num=1,
        task_label="请求初始字体映射",
        allow_validated_resume=not args.force,
        force_download=args.force,
        skip_download=args.skip_download,
        race_copies=args.race_copies,
    )
    all_commands.append(commands_text)
    validated_responses.append(validated_raw)
    validation_reports.append(validation_report)

    unresolved_keys: set[str] = set()
    for key, decision in round_decisions.items():
        if decision is not None:
            final_decisions[key] = decision
        elif font_records[key].pages <= selected_page_set:
            final_decisions[key] = None
        else:
            unresolved_keys.add(key)

    evidence_round = 1
    while unresolved_keys:
        evidence_round += 1

        additional_pages = select_additional_evidence_pages(
            unresolved_keys=unresolved_keys,
            page_stats=page_stats,
            already_selected=selected_page_set,
        )

        if not additional_pages:
            remaining_pages = {
                key: sorted(font_records[key].pages - selected_page_set)
                for key in sorted(unresolved_keys, key=lambda value: value.casefold())
                if font_records[key].pages - selected_page_set
            }
            raise RuntimeError(
                "仍有字体尚未检查全部出现页面，但无法选出补充页面："
                f"{remaining_pages}"
            )

        print(
            f"\n=== 第 {evidence_round} 轮补充证据："
            f"为 {len(unresolved_keys)} 个未决字体新增页面 {additional_pages} ==="
        )
        split_selected_pages(
            pdf_path=pdf_path,
            pages_dir=pages_dir,
            selected_pages=additional_pages,
            force=args.force,
        )
        if not args.skip_upload:
            upload_selected_pages_to_github(
                pages_dir=pages_dir,
                selected_pages=additional_pages,
                folder_name=github_folder,
                repo_url=github_repo_url,
                branch=github_branch,
                push_retry=github_push_retry,
            )
        else:
            print("已按 --skip-upload 跳过补充代表页的 GitHub 上传。")

        selected_page_set.update(additional_pages)
        selected_pages = sorted(selected_page_set)
        write_selected_pages_file(work_dir, selected_pages)

        followup_prompt = build_followup_prompt(
            round_num=evidence_round,
            unresolved_keys=unresolved_keys,
            all_selected_pages=selected_pages,
            font_records=font_records,
            page_stats=page_stats,
            repo_url=github_repo_url,
            branch=github_branch,
            folder_name=github_folder,
        )

        (
            commands_text,
            round_decisions,
            validation_report,
            validated_raw,
        ) = request_locally_validated_mapping_round(
            base_prompt=followup_prompt,
            expected_keys=unresolved_keys,
            work_dir=work_dir,
            output_root=output_root,
            round_num=evidence_round,
            task_label=f"请求第 {evidence_round} 轮字体补充判断",
            allow_validated_resume=not args.force,
            force_download=args.force,
            skip_download=args.skip_download,
            race_copies=args.race_copies,
        )
        all_commands.append(commands_text)
        validated_responses.append(validated_raw)
        validation_reports.append(validation_report)

        next_unresolved: set[str] = set()
        for key, decision in round_decisions.items():
            if decision is not None:
                final_decisions[key] = decision
            elif font_records[key].pages <= selected_page_set:
                final_decisions[key] = None
            else:
                next_unresolved.add(key)

        unresolved_keys = next_unresolved

    if set(final_decisions) != set(font_records):
        missing = sorted(set(font_records) - set(final_decisions))
        extra = sorted(set(final_decisions) - set(font_records))
        raise RuntimeError(f"最终字体决策键集合不完整；缺少={missing}；多余={extra}")

    combined_commands_text = "\n".join(
        block.strip()
        for block in all_commands
        if block.strip()
    )

    if args.skip_download:
        font_metadata: dict[str, dict[str, Any]] = {}
        print("⚠ 已按 --skip-download 跳过生产环境字体下载和字形验证")
    else:
        font_metadata = ensure_mapping_fonts(
            mappings=final_decisions,
            commands_text=combined_commands_text,
            output_root=output_root,
            force_download=args.force,
        )

    rejected_candidates = load_rejected_font_candidates(work_dir)
    save_final_mapping(
        output_root=output_root,
        pdf_path=pdf_path,
        selected_pages=selected_pages,
        mappings=final_decisions,
        font_metadata=font_metadata,
        commands_text=combined_commands_text,
        validated_responses=validated_responses,
        validation_reports=validation_reports,
        rejected_candidates=rejected_candidates,
        local_validation_completed=not args.skip_download,
        work_dir=work_dir,
    )

    final_print_payload = {
        "version": 3,
        "mappings": {
            key: (
                {
                    "target_font_file": decision.target_font_file,
                    "download_url": decision.download_url,
                }
                if decision is not None
                else None
            )
            for key, decision in sorted(
                final_decisions.items(),
                key=lambda item: item[0].casefold(),
            )
        },
    }

    print("\n=== 模型生成的最终映射 ===")
    print(json.dumps(final_print_payload, ensure_ascii=False, indent=2))
    print("=" * 72)
    print("=== 阶段 0 完成 ===")
    print("=" * 72)


if __name__ == "__main__":
    main()

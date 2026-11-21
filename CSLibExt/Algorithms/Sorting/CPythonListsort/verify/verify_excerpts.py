#!/usr/bin/env python3
"""Generate and verify the pinned CPython listsort source corpus.

The Markdown files produced here are review artifacts.  Every C code block is
selected from the pinned upstream bytes; this script never reformats or
reconstructs C source.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
import urllib.request
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CPYTHON_COMMIT = "67e6be72be9c0b75a31795ed42f9afb5eb431d47"
CPYTHON_RAW = f"https://raw.githubusercontent.com/python/cpython/{CPYTHON_COMMIT}"
LISTOBJECT_PATH = "Objects/listobject.c"
LISTSORT_PATH = "Objects/listsort.txt"


@dataclass(frozen=True)
class Excerpt:
    slug: str
    title: str
    start: int
    end: int
    body: str


def fetch(path: str) -> bytes:
    request = urllib.request.Request(
        f"{CPYTHON_RAW}/{path}", headers={"User-Agent": "cpython-listsort-lean"}
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        return response.read()


def leading_comment_start(lines: list[str], start: int) -> int:
    """Include an immediately adjacent C block comment, if present."""
    cursor = start - 1
    if cursor < 0 or not lines[cursor].rstrip().endswith("*/"):
        return start
    while cursor >= 0:
        if "/*" in lines[cursor]:
            return cursor
        cursor -= 1
    raise ValueError(f"unterminated leading comment before line {start + 1}")


def definition_start(lines: list[str], name: str) -> int:
    name_line = next(
        (
            index
            for index, line in enumerate(lines)
            if re.match(rf"^{re.escape(name)}\s*\(", line.strip())
        ),
        None,
    )
    if name_line is None:
        raise ValueError(f"definition not found: {name}")

    start = name_line
    previous = lines[start - 1].strip() if start else ""
    if (
        previous.startswith("static ")
        or previous.startswith("Py_LOCAL_INLINE(")
        or previous.startswith("PyObject *")
    ):
        start -= 1
    return leading_comment_start(lines, start)


def definition_end(lines: list[str], start: int, name: str) -> int:
    """Return the inclusive ending line, ignoring braces in C comments/strings."""
    depth = 0
    opened = False
    in_block_comment = False
    in_string: str | None = None
    escaped = False

    for line_index in range(start, len(lines)):
        line = lines[line_index]
        in_line_comment = False
        char_index = 0
        while char_index < len(line):
            char = line[char_index]
            following = line[char_index + 1] if char_index + 1 < len(line) else ""

            if in_line_comment:
                break
            if in_block_comment:
                if char == "*" and following == "/":
                    in_block_comment = False
                    char_index += 2
                    continue
                char_index += 1
                continue
            if in_string is not None:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == in_string:
                    in_string = None
                char_index += 1
                continue
            if char == "/" and following == "*":
                in_block_comment = True
                char_index += 2
                continue
            if char == "/" and following == "/":
                in_line_comment = True
                break
            if char in {'"', "'"}:
                in_string = char
                char_index += 1
                continue
            if char == "{":
                opened = True
                depth += 1
            elif char == "}" and opened:
                depth -= 1
                if depth == 0:
                    return line_index
            char_index += 1
    raise ValueError(f"closing brace not found: {name}")


def function_excerpt(lines: list[str], name: str, title: str | None = None) -> Excerpt:
    start = definition_start(lines, name)
    end = definition_end(lines, start, name)
    return Excerpt(
        slug=name.replace("_", "-"),
        title=title or f"`{name}`",
        start=start + 1,
        end=end + 1,
        body="".join(lines[start : end + 1]),
    )


def merge_state_excerpt(lines: list[str]) -> Excerpt:
    constant = next(
        index for index, line in enumerate(lines) if line.startswith("#define MAX_MERGE_PENDING")
    )
    start = leading_comment_start(lines, constant)
    field = next(
        index for index, line in enumerate(lines) if "Py_ssize_t mr_current, mr_e, mr_mask;" in line
    )
    end = next(index for index in range(field + 1, len(lines)) if lines[index].strip() == "};")
    return Excerpt(
        slug="merge-state",
        title="Sorting constants and `MergeState` layout",
        start=start + 1,
        end=end + 1,
        body="".join(lines[start : end + 1]),
    )


def sortslice_excerpt(lines: list[str]) -> Excerpt:
    start = next(
        index for index, line in enumerate(lines) if line.startswith("/* A sortslice contains")
    )
    operation_start = definition_start(lines, "sortslice_advance")
    end = definition_end(lines, operation_start, "sortslice_advance")
    return Excerpt(
        slug="sortslice-primitives",
        title="`sortslice` layout and synchronized movement primitives",
        start=start + 1,
        end=end + 1,
        body="".join(lines[start : end + 1]),
    )


def comparison_macros_excerpt(lines: list[str]) -> Excerpt:
    start = next(
        index for index, line in enumerate(lines) if line.startswith("/* Comparison function:")
    )
    iflt = next(index for index, line in enumerate(lines) if line.startswith("#define IFLT"))
    end = iflt
    while lines[end].rstrip().endswith("\\"):
        end += 1
    return Excerpt(
        slug="comparison-dispatch",
        title="Comparator dispatch macros",
        start=start + 1,
        end=end + 1,
        body="".join(lines[start : end + 1]),
    )


def merge_getmem_macro_excerpt(lines: list[str]) -> Excerpt:
    start = next(
        index
        for index, line in enumerate(lines)
        if line.startswith("#define MERGE_GETMEM")
    )
    end = start
    while lines[end].rstrip().endswith("\\"):
        end += 1
    return Excerpt(
        slug="merge-getmem-macro",
        title="`MERGE_GETMEM` dispatch macro",
        start=start + 1,
        end=end + 1,
        body="".join(lines[start : end + 1]),
    )


def derive_excerpts(source: bytes) -> list[Excerpt]:
    text = source.decode("utf-8")
    lines = text.splitlines(keepends=True)
    names = [
        "list_resize",
        "reverse_slice",
        "sortslice_reverse",
        "merge_init",
        "minrun_next",
        "powerloop",
        "binarysort",
        "count_run",
        "gallop_left",
        "gallop_right",
        "merge_freemem",
        "merge_getmem",
        "merge_lo",
        "merge_hi",
        "merge_at",
        "found_new_run",
        "merge_force_collapse",
        "list_sort_impl",
    ]
    excerpts = [
        sortslice_excerpt(lines),
        comparison_macros_excerpt(lines),
        merge_state_excerpt(lines),
    ]
    for name in names:
        excerpts.append(function_excerpt(lines, name))
        if name == "merge_getmem":
            excerpts.append(merge_getmem_macro_excerpt(lines))
    return excerpts


def render_excerpts(source: bytes) -> bytes:
    parts = [
        "# CPython listsort excerpts\n\n",
        f"Pinned CPython commit: [`{CPYTHON_COMMIT}`](https://github.com/python/cpython/commit/{CPYTHON_COMMIT})\n\n",
        f"Upstream file: [`{LISTOBJECT_PATH}`](https://github.com/python/cpython/blob/{CPYTHON_COMMIT}/{LISTOBJECT_PATH})\n\n",
        "The C excerpts below are copied verbatim from the pinned upstream file. ",
        "Their selection and byte identity are checked by `verify/verify_excerpts.py`. ",
        "CPython is distributed under the Python Software Foundation License Version 2; ",
        "the excerpted C remains subject to that license.\n\n",
        "## Version-one modeling boundary\n\n",
        "The Lean model uses a pure total `α → α → Bool` comparator and therefore ",
        "excludes exception propagation and comparator side effects. It starts from an ",
        "immutable snapshot of already-computed keys paired with payloads; key-function ",
        "evaluation, mutation during sorting, allocator failure paths, interpreter ",
        "reentrancy, the compiler, and lower-level runtime behavior are outside version one.\n\n",
    ]
    for excerpt in derive_excerpts(source):
        parts.extend(
            [
                f"## {excerpt.title} {{#{excerpt.slug}}}\n\n",
                f"Upstream lines {excerpt.start}-{excerpt.end}.\n\n",
                f"<!-- autoform-excerpt source={LISTOBJECT_PATH} lines={excerpt.start}-{excerpt.end} sha={CPYTHON_COMMIT} -->\n\n",
                "```c\n",
                excerpt.body,
                "```\n\n",
            ]
        )
    return ("".join(parts).rstrip("\n") + "\n").encode("utf-8")


def render_listsort(source: bytes) -> bytes:
    header = (
        "# CPython listsort design notes\n\n"
        f"Pinned CPython commit: [`{CPYTHON_COMMIT}`](https://github.com/python/cpython/commit/{CPYTHON_COMMIT})\n\n"
        f"Upstream file: [`{LISTSORT_PATH}`](https://github.com/python/cpython/blob/{CPYTHON_COMMIT}/{LISTSORT_PATH})\n\n"
        "Everything following this header is the verbatim upstream file. CPython is "
        "distributed under the Python Software Foundation License Version 2.\n\n"
    ).encode("utf-8")
    return header + source


def compare(path: Path, expected: bytes) -> bool:
    try:
        display_path = path.resolve().relative_to(ROOT.resolve())
    except ValueError:
        display_path = path
    if not path.exists():
        print(f"missing generated source: {display_path}", file=sys.stderr)
        return False
    actual = path.read_bytes()
    if actual == expected:
        print(f"verified {display_path}")
        return True
    diff = difflib.unified_diff(
        actual.decode("utf-8", errors="replace").splitlines(),
        expected.decode("utf-8", errors="replace").splitlines(),
        fromfile=str(display_path),
        tofile=f"expected:{display_path}",
        lineterm="",
    )
    print("\n".join(diff), file=sys.stderr)
    return False


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=ROOT / "sources",
        help="directory containing listobject-excerpts.md and listsort.md",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="regenerate the two Markdown sources before verifying them",
    )
    args = parser.parse_args()

    listobject = fetch(LISTOBJECT_PATH)
    listsort = fetch(LISTSORT_PATH)
    expected = {
        args.output_dir / "listobject-excerpts.md": render_excerpts(listobject),
        args.output_dir / "listsort.md": render_listsort(listsort),
    }
    if args.write:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for path, content in expected.items():
            path.write_bytes(content)
            print(f"wrote {path}")

    return 0 if all(compare(path, content) for path, content in expected.items()) else 1


if __name__ == "__main__":
    raise SystemExit(main())

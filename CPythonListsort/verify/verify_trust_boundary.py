#!/usr/bin/env python3
"""Reject unreviewed `native_decide` uses or dependencies on their results."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

# These declarations are executable review witnesses, not proof dependencies.
# Any addition or removal requires updating the roadmap trust ledger first.
EXPECTED = {
    (
        "Code/Transcription/MergeAt.lean",
        "mergeAt_slide_regression",
    ),
    (
        "Code/Correctness/MergeAtCorrectness.lean",
        "mergeAt_thirdLast_slide_regression",
    ),
    (
        "Code/Correctness/FoundNewRunCorrectness.lean",
        "foundNewRunLoop_taken_merge_regression",
    ),
    (
        "Code/Correctness/MergeForceCollapseCorrectness.lean",
        "mergeForceCollapse_threeRun_equalKey_payload_regression",
    ),
    (
        "Code/Correctness/ScanStepCorrectness.lean",
        "listSortScan_long_run_no_extension_regression",
    ),
    (
        "Code/Correctness/ScanStepCorrectness.lean",
        "listSortScan_policy_merge_then_push_regression",
    ),
    (
        "Code/Correctness/ListSortCorrectness.lean",
        "listSort_forward_keyed_duplicate_exact_regression",
    ),
    (
        "Code/Correctness/ListSortCorrectness.lean",
        "listSort_reverse_keyed_duplicate_exact_regression",
    ),
    (
        "Code/Assembly/MergeMemorySafety.lean",
        "listSort_mergeMemory_lo_event_regression",
    ),
    (
        "Code/Assembly/MergeMemorySafety.lean",
        "listSort_mergeMemory_hi_event_regression",
    ),
    (
        "Code/Assembly/MergeMemorySafety.lean",
        "listSort_mergeMemory_released_growth_regression",
    ),
    (
        "Code/Assembly/PowerSortCostRegression.lean",
        "listSort_powerSort_cost_rotation_regression",
    ),
}

NAMED_DECL = re.compile(
    r"^\s*(?:private\s+)?(?:theorem|lemma|example)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b"
)
ANONYMOUS_EXAMPLE = re.compile(r"^\s*example\s*:")


def lean_files() -> list[Path]:
    files = sorted((ROOT / "Code").rglob("*.lean"))
    files.append(ROOT / "Code.lean")
    return files


def main() -> int:
    observed: set[tuple[str, str]] = set()
    errors: list[str] = []
    texts: dict[Path, str] = {}

    for path in lean_files():
        text = path.read_text(encoding="utf-8")
        texts[path] = text
        current_decl: str | None = None
        for line_no, line in enumerate(text.splitlines(), start=1):
            match = NAMED_DECL.match(line)
            if match:
                current_decl = match.group(1)
            elif ANONYMOUS_EXAMPLE.match(line):
                current_decl = None
            if "native_decide" not in line:
                continue
            rel = path.relative_to(ROOT).as_posix()
            if current_decl is None:
                errors.append(f"{rel}:{line_no}: native_decide is not in a named declaration")
                continue
            observed.add((rel, current_decl))

    for missing in sorted(EXPECTED - observed):
        errors.append(f"missing allowlisted native_decide regression: {missing[0]}::{missing[1]}")
    for extra in sorted(observed - EXPECTED):
        errors.append(f"unreviewed native_decide declaration: {extra[0]}::{extra[1]}")

    # A compiler-checked witness must remain a leaf: its name may occur only at
    # its own declaration, never in another Lean proof or definition.
    corpus = "\n".join(texts.values())
    for _path, name in sorted(EXPECTED):
        uses = len(re.findall(rf"\b{re.escape(name)}\b", corpus))
        if uses != 1:
            errors.append(
                f"compiler-checked regression {name} has {uses} Lean occurrences; expected only its declaration"
            )

    if errors:
        print("trust-boundary verification failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print(
        "verified native_decide trust boundary: "
        f"{len(EXPECTED)} named compiler-checked regressions, no Lean consumers"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.countRun?
---

# `count_run`

Transcribe natural-run detection, including handling of equal sub-runs in a
descending run and reversal to an ascending run. Preserve comparison call
order because the v1 comparator may be inconsistent even though it is total.

## Depends on

- [sortslice model and movement primitives](sortslice-primitives.md)
- [MergeState and pending runs](merge-state.md)
- [Slice reversal](reverse-slice.md)

## Sources

- [Verbatim `count_run`](../../sources/listobject-excerpts.md#count-run)
- [CPython run explanation](../../sources/listsort.md#runs)

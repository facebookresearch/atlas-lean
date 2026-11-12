---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.mergeForceCollapse?
---

# `merge_force_collapse`

Transcribe the final loop that repeatedly selects one of the top two adjacent
merge positions based on neighboring lengths and calls `merge_at` until one
pending run remains.

## Depends on

- [MergeState and pending runs](merge-state.md)
- [merge_at](merge-at.md)

## Sources

- [Verbatim `merge_force_collapse`](../../sources/listobject-excerpts.md#merge-force-collapse)

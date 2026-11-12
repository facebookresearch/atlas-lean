---
declaration: def
origin: bridged
statement: formalized
lean: CPythonListsort.PendingLayout
---

# Pending-run layout invariant

Define `PendingLayout`: pending runs are nonempty, individually within the
input, pairwise adjacent in index order, and together cover exactly the
already-scanned prefix. The predicate does not inspect powers or mention
comparator laws. Its scanned-prefix interpretation is sourced from
`list_sort_impl`: the loop calls `found_new_run` at the current `lo`, pushes
that run, then advances `lo` and decreases `nremaining`, so the pending stack
tiles precisely the prefix already traversed by that scan.

## Depends on

- [MergeState and pending runs](../transcription/merge-state.md)

## Sources

- [Verbatim `MergeState`](../../sources/listobject-excerpts.md#merge-state)
- [Verbatim `list_sort_impl`](../../sources/listobject-excerpts.md#list-sort-impl)

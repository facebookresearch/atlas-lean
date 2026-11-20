---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.mergeFreemem
---

# `merge_freemem`

Transcribe the observable model transition that releases non-inline temporary
storage. Non-inline payload cells become inaccessible, but `alloced` and
`hasValues` remain unchanged, matching the C fields left stale by this
function. Raw deallocation and allocator behavior remain outside the theorem
boundary. Preservation and liveness claims are separate safety nodes.

## Depends on

- [MergeState and pending runs](merge-state.md)

## Sources

- [Verbatim `merge_freemem`](../../sources/listobject-excerpts.md#merge-freemem)
- [Modeling boundary](../../sources/toplevel-theorems.md#explicit-scope-boundary)

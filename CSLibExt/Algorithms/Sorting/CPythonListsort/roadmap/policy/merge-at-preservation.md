---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeAt_preserves_pendingLayout
---

# `merge_at` preserves pending layout

For either stack index admitted by CPython's assertions, prove that a successful
`merge_at` replaces two adjacent nonempty runs by their nonempty union,
preserves all other pending runs, and preserves `PendingLayout` with the same
covered prefix. The statement makes no ordering assumption on the comparator.

## Depends on

- [Pending-run layout invariant](pending-layout.md)
- [merge_at](../transcription/merge-at.md)

## Sources

- [Verbatim `merge_at`](../../sources/listobject-excerpts.md#merge-at)

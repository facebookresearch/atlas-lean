---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeFreemem_tempStorageInv
---

# `merge_freemem` preserves temporary-storage validity

Given `TempStorageInv` before `merge_freemem`, prove it afterward. Inline
storage is unchanged. Non-inline storage becomes `.released` with no payload
cells, while `alloced` and `hasValues` remain available as stale metadata.
This theorem is a representation-preservation result only: it does not permit
payload access after release.

## Depends on

- [The `merge_freemem` transcription](../../transcription/merge-freemem.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)

## Sources

- [Verbatim `merge_freemem`](../../../sources/listobject-excerpts.md#merge-freemem)

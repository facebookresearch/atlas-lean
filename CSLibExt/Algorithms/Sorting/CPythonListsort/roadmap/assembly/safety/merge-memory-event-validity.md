---
declaration: structure
origin: bridged
statement: formalized
lean: CPythonListsort.MergeMemoryCallEvent.Valid
---

# Merge-memory event validity and continuous-segment support

Define the semantic vocabulary used before top-level lifecycle assembly.  Raw
`MergeMemorySnapshot`, `MergeMemoryCallEvent`, and `MergeMemoryEvent` values are
non-validating observations in the real `AccessTrace`; this node supplies the
separate propositions which make those observations meaningful.

`MergeMemorySnapshot.StorageInv`, `Live`, `ValuesMode`, `ActiveCore`, and
`PhysicalBound` are defined at
`Code/Assembly/MergeMemoryLifecycle.lean:33`, `:44`, `:50`, `:58`,
and `:64`.  `ActiveCore` contains the snapshot form of `TempStorageInv`, live
backing, exact logical capacity, and the concrete keyed/unkeyed values mode;
the selected-platform physical ceiling remains a separate reachability fact.

The headline `MergeMemoryCallEvent.Valid` structure is stated at
`Code/Assembly/MergeMemoryLifecycle.lean:421`.  It requires:

- active storage before allocation, after `merge_getmem`, and after the merge;
- the exact request `min na nb`, with `merge_lo` selecting `na ≤ nb` and
  `merge_hi` selecting `nb < na`;
- shrink-only trimming and the source-run bound through `listlen`;
- `request ≤ ⌊(na + nb)/2⌋ ≤ ⌊listlen/2⌋`;
- the keyed limit `2^59 - 1` and unkeyed limit `2^60 - 1`;
- successful reuse-or-growth semantics, exclusion of `.guardRejected`, and
  exact key/value physical-slot bounds; and
- preservation of storage metadata and the physical ceiling.

The literal lo and hi call records satisfy this complete structure by
`mergeLoMemoryCallEvent_valid` and `mergeHiMemoryCallEvent_valid` at
`Code/Assembly/MergeMemoryLifecycle.lean:523` and `:617`.
`MergeMemoryCallEvent.Bounded` at
`Code/Assembly/MergeMemoryLifecycle.lean:706` separately covers the
incoming, post-allocation, post-merge, and optional intermediate-free physical
snapshots; the reviewed directional posts establish it at lines 777 and 794.

The same support layer defines the exact continuity predicates consumed by
the callers: `MergeMemoryCallChain` at line 867,
`AccessTrace.MergeMemorySegment` at line 934, and
`AccessTrace.MergeMemoryTail` at line 943.  In particular, an empty segment
can connect only equal snapshots, and every nonempty segment equates each
call's `before` snapshot with the preceding concrete endpoint.  The theorem
`MergeMemoryCallChain.rejects_two_call_gap` at line 905 rejects a fabricated
two-call history with a mismatched boundary.

This upstream support node also owns the shape predicate
`AccessTrace.MergeMemoryLifecycle`, defined at
`Code/Assembly/MergeMemoryLifecycle.lean:1023`: one initializer, a
gap-free call chain, and one cleanup, with the same call list required to be
`Valid` and `Bounded`. The downstream lifecycle-witness node owns only the
theorem that the real top-level execution inhabits this predicate.

This is deliberately a pre-`merge_at` support node.  The separate
[top-level lifecycle witness](merge-memory-lifecycle.md) is proved only after
the scan and termination assembly; no dependency edge points backward from
this support vocabulary to that top-level theorem.

## Depends on

- [Array-access, push-depth, and merge-memory trace model](access-trace.md)
- [MergeState and pending runs](../../transcription/merge-state.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [`merge_getmem`](../../transcription/merge-getmem.md)
- [`merge_freemem`](../../transcription/merge-freemem.md)

## Proof depends on

- [`merge_freemem` preserves temporary-storage validity](merge-freemem-storage-valid.md)
- [`merge_getmem` call-site request bound](merge-getmem-request-bound.md)
- [`merge_getmem` establishes live temporary capacity](merge-getmem-storage-valid.md)
- [`merge_lo` safety](merge-lo-safe.md)
- [`merge_hi` safety](merge-hi-safe.md)

## Sources

- [Verbatim `merge_init`](../../../sources/listobject-excerpts.md#merge-init)
- [Verbatim `merge_freemem`](../../../sources/listobject-excerpts.md#merge-freemem)
- [Verbatim `merge_getmem`](../../../sources/listobject-excerpts.md#merge-getmem)
- [Verbatim `MERGE_GETMEM`](../../../sources/listobject-excerpts.md#merge-getmem-macro)
- [Verbatim `merge_at`](../../../sources/listobject-excerpts.md#merge-at)

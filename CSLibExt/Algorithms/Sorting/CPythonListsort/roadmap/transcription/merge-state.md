---
declaration: structure
origin: cited
statement: formalized
lean: CPythonListsort.MergeState
---

# `MergeState` and pending runs

Transcribe list length, pending runs and their powers, galloping threshold,
temporary storage abstraction, and adaptive-minrun fields. Preserve the C field
names where Lean permits them. Comparator specialization pointers and raw
allocation state are replaced by the explicit v1 abstractions documented in
the source boundary.

The raw structure deliberately admits arbitrary field combinations. The
adjacent `TempStorageInv` support definition states the relationship maintained
by `merge_init`, `merge_getmem`, merge operations, and `merge_freemem`; users
must not infer payload capacity from `alloced` alone.

Represent the active pending stack as an unbounded `Array PendingRun`, with
`ms.n` derived from its size. This is deliberately not a capacity-enforcing
representation: `MAX_MERGE_PENDING` appears in the later trace theorem, not in
the array's type or a guarded push.

## Depends on

- [sortslice model and movement primitives](sortslice-primitives.md)
- [Total Boolean comparator model](comparator-model.md)

## Sources

- [Verbatim constants and `MergeState`](../../sources/listobject-excerpts.md#merge-state)
- [Modeling boundary](../../sources/toplevel-theorems.md#explicit-scope-boundary)

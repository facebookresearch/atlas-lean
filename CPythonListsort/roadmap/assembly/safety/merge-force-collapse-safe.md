---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeForceCollapse_safe
---

# `merge_force_collapse` safety

From a nonempty valid pending layout, prove that `merge_force_collapse`
terminates, inspects only live neighboring lengths, chooses one of the two
allowed merge indices, and keeps every delegated access in bounds for an
arbitrary total Boolean comparator. Require
`SortSlice.ValuesModeInvariant state.a.hasValues state.data` at entry and
return it at exit; each iteration obtains preservation from the delegated
`merge_at` call. Independently return
`result.state.a.hasValues = state.a.hasValues`, chaining `merge_at`'s frame
equation through the collapse loop rather than inferring the mode bit from a
possibly vacuous invariant on empty data.

Require the active temporary-storage package at entry as well:
`TempStorageInv state.a state.alloced` together with `state.a.Live`. Preserve
both facts across every collapse iteration and return them for the final state.
Each delegated `merge_at` call supplies the inductive step, including branches
that grow temporary storage, so the result can be consumed directly by final
top-level cleanup.

Define the traced `merge_force_collapse` evaluator here and, for the same
source-admitted invariant-bearing calls, prove exact erasure to
`mergeForceCollapse?`, preserving pending-access and delegated merge event
order. (No stronger off-domain erasure claim is inherited from the reviewed
`merge_at` safety node.) Return
`execution.trace.tempPayloadAccessesLive` by composing the property from every
delegated `merge_at` trace.

The public post now also exports event validity, directional-only
classification, all-call physical boundedness from the incoming initializer
bound, final-bound preservation, and a continuous merge-memory segment. Those
fields are stated at
`Code/Assembly/MergeForceCollapseSafety.lean:703`,
`Code/Assembly/MergeForceCollapseSafety.lean:705`,
`Code/Assembly/MergeForceCollapseSafety.lean:707`,
`Code/Assembly/MergeForceCollapseSafety.lean:710`, and
`Code/Assembly/MergeForceCollapseSafety.lean:713`; the existing
`mergeForceCollapse_safe` theorem at
`Code/Assembly/MergeForceCollapseSafety.lean:729` produces them
without a new public premise. The reusable theorem that concatenates two
continuous segments exactly at their shared state is
`AccessTrace.mergeMemorySegment_compose` at
`Code/Assembly/MergeMemoryLifecycle.lean:994`.

## Depends on

- [Array-access trace model](access-trace.md)
- [Merge-memory event validity and continuous-segment support](merge-memory-event-validity.md)
- [Pending-run layout invariant](../../policy/pending-layout.md)
- [merge_force_collapse](../../transcription/merge-force-collapse.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [sortslice primitive safety](sortslice-safe.md)

## Proof depends on

- [merge_at safety](merge-at-safe.md)
- [merge_force_collapse preserves layout](../../policy/force-collapse-preservation.md)

## Sources

- [Verbatim `merge_force_collapse`](../../../sources/listobject-excerpts.md#merge-force-collapse)

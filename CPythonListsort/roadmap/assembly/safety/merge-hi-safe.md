---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeHi_safe
---

# `merge_hi` safety

For a call selected by `merge_at`, let `pre` be its entry state satisfying
`PendingLayout` and `pre.listlen.toNat ≤ PY_LIST_MAX`, let the post-trimming
adjacent nonempty runs satisfy `na > nb`, and let the call-state temporary
storage satisfy `TempStorageInv` with `backing ≠ .released`. Require the
main slice to satisfy `SortSlice.ValuesModeInvariant` for the storage's
explicit `hasValues` mode. Prove that
`merge_hi` obtains enough temporary capacity, preserves the representation
and values-mode invariants and live backing, returns success without exhausting
either merge or trace fuel, terminates in ordinary and galloping modes, and
keeps every decrementing source, destination, and temporary access in bounds
for an arbitrary comparator. Also export the stable state frame for `listlen`,
`basekeys`, data extent, the temporary-storage `hasValues` mode, pending stack,
comparator, and adaptive-minrun fields. In particular,
`result.state.a.hasValues = call.state.a.hasValues` is available independently
of the values-mode invariant, including when the data slice is empty.

The run-span fact `call.na + call.nb ≤ pre.listlen.toNat` is derived from
the pending runs tiling the scanned prefix and from gallop trimming decreasing
lengths; it is not an unrelated caller assumption. The request-bound theorem
then supplies the exact `call.nb ≤ pre.listlen.toNat / 2` allocation
inequality. No ordering or endpoint-value premise is used. The live-storage
premise is explicit in this local theorem. The top-level execution induction
discharges it from the preceding active state and carries the returned
liveness fact to the next helper call. The global liveness node only
projects the already-composed whole-execution trace property; it is not a
premise of this theorem.

Define the traced `merge_hi` evaluator here and prove exact erasure to
`mergeHi?`. All main-data and temporary-payload operations use their typed
trace primitives. Temporary gallops use the key-source interface rather than
probing a materialized temporary `SortSlice`, so they neither mislabel nor
double-record accesses. The public postcondition requires return code zero,
both fuel flags false, an empty push-depth trace, exact erasure to `mergeHi?`,
and witnesses for a main-key event and for temporary writes and reads. In keyed
mode it also requires a synchronized-values event. These witnesses rule out an
empty decorative trace and make temporary-access liveness non-vacuous.

Every `memcpy`-class bulk movement must also occur at a site covered by the
exported merge call-site classification and carry `distinctBacking`
provenance.  The proof consumes that theorem, including the `sortslice`
admissibility gate and same-backing overlap rejection; it does not recover
pointer separation from the evaluator's private helper shape.

## Depends on

- [Array-access trace model](access-trace.md)
- [Pending-run layout invariant](../../policy/pending-layout.md)
- [Finite-width implementation model](../../transcription/word-model.md)
- [The `merge_at` transcription](../../transcription/merge-at.md)
- [merge_hi](../../transcription/merge-hi.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [`sortslice` access safety](sortslice-safe.md)
- [`merge_getmem` call-site request bound](merge-getmem-request-bound.md)
- [Merge `memcpy` call-site provenance](merge-memcpy-provenance.md)

## Proof depends on

- [gallop_left safety](gallop-left-safe.md)
- [gallop_right safety](gallop-right-safe.md)
- [`merge_getmem` establishes live temporary capacity](merge-getmem-storage-valid.md)

## Sources

- [Verbatim `merge_hi`](../../../sources/listobject-excerpts.md#merge-hi)

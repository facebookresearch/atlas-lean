---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listsort_safe
---

# `listsort_safe`

For either value of the `reverse` flag, any total Boolean comparator, and an
input of size at most `PY_LIST_MAX`, the traced evaluator returns `some result`,
does not exhaust fuel, records only in-bounds indexed access events, records
every pending-stack push, and satisfies
`trace.stackDepthMax ≤ 61 ∧ 61 < MAX_MERGE_PENDING`. Here `stackDepthMax` is the
maximum recorded post-push depth. No ordering hypothesis is permitted. Export
result existence explicitly rather than asking consumers to infer completion
from `trace.fuelExhausted = false`; neither claim may be replaced by mere
totality of the bounded evaluator.

State this public theorem over the `listSortTraced?` evaluator for the
formalized proof-carrying `ListSortInput`, not for an unconstrained raw
`SortSlice`. Its array smart constructor fixes the keyed or unkeyed
representation mode and supplies the initial `ValuesModeInvariant`; fuel
adequacy and local bounds then consume both the invariant-preservation chain
and the independent `a.hasValues` frame equalities. A separate generalized
theorem about raw `listSortImplTraced?` may be exported, but it must retain
`ValuesModeInvariant hasKeyfunc input` as a premise rather than pretending
every raw model state is reachable from C.

The push used by the evaluator is unconditional `Array.push`, even at depth 64,
and would record 65. The proof must derive the bound from the policy invariant;
it must not use a capacity guard, failed mutation, or debug-assertion event.

The top-level loop invariant and its field-by-field consumer diff are published
on the [fuel-adequacy node](termination.md#loop-invariant-consumer-diff). The
assembly did not retrofit any conclusion into the approved
`FoundNewRunSafetyPost` contract.

`listsort_safe_keyed` and `listsort_safe_unkeyed` are constructor-specific
corollaries of this same theorem. Neither adds a values-mode or liveness
premise; each obtains those facts from the corresponding validated
`ListSortInput` constructor
(`Code/Assembly/ListSortSafety.lean:30` and `:43`).

## Depends on

- [Array-access and push-depth trace model](access-trace.md)
- [Finite-width implementation model](../../transcription/word-model.md)
- [sortslice primitive safety](sortslice-safe.md)
- [list_sort_impl fuel adequacy](termination.md)

## Proof depends on

- [list_sort_impl access bounds](local-bounds.md)

## Sources

- [Comparator-independent safety theorem contract](../../../sources/toplevel-theorems.md#comparator-independent-safety)

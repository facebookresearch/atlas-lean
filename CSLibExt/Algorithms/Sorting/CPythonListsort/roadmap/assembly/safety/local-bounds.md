---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listSortImplTraced_allAccessesInBounds
---

# `list_sort_impl` access bounds

For an arbitrary comparator and `xs.size ≤ PY_LIST_MAX`, prove that every
ordinary array-access event in the complete, fuel-adequate `list_sort_impl`
trace lies inside the array extent recorded at that event. This is a single
composition theorem over the per-function safety lemmas; signed arithmetic and
temporary storage are discharged in those local results. Pending-stack pushes
are total unbounded `Array.push` operations and are handled separately by their
recorded post-push depths and the strict stack-depth theorem. This proof may not
rely on a push refusing to mutate or on a capacity-failure branch.

For the generalized raw evaluator, take the same explicit
`SortSlice.ValuesModeInvariant hasKeyfunc input` premise as fuel adequacy and
consume each local node's preservation result while composing the trace. For
the public proof-carrying `listSortTraced?` wrapper, discharge that premise
with the `ListSortInput.unkeyed`, `ListSortInput.unkeyedAs`, or
`ListSortInput.keyed` smart-constructor proof. Consume the separate
`a.hasValues` frame equality throughout the composition as well; do not infer
the mode bit from an invariant that may be vacuous. Thus synchronized-values
events are justified from the initial representation through every
data-changing helper; they are not made well-formed only at the individual
movement calls.

The public theorem consumes the `listSortTraced?` evaluator and its exact
erasure theorem assembled by the fuel-adequacy node. The generalized raw
theorem consumes `listSortImplTraced?` and retains `hMode`. Neither theorem
constructs a second trace or infers events from the final state. In Lean this
node is a projection of the whole-execution certificate already assembled by
fuel adequacy; it does not depend on the independent aggregate
`merge-memory-safe` history theorem.

## Depends on

- [Array-access and push-depth trace model](access-trace.md)
- [list_sort_impl fuel adequacy](termination.md)

## Sources

- [Safety theorem contract](../../../sources/toplevel-theorems.md#comparator-independent-safety)
- [Verified C excerpts](../../../sources/listobject-excerpts.md)

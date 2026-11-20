---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listSortImplTraced_safe
---

# `list_sort_impl` fuel adequacy

For every comparator and input with `xs.size ≤ PY_LIST_MAX`, prove that the
bounded top-level scan consumes the remaining suffix, returns `some result`, and
produces a trace with `fuelExhausted = false`. Combined with the separately
proved helper-safety and policy-termination theorems, this establishes one
public completion-and-adequacy result for `list_sort_impl`; no downstream
theorem depends on a `partial` definition, an unproved exhaustion case, or the
absence of an unrelated failure arm.

State the generalized theorem for raw `listSortImpl?` with the explicit
premise `SortSlice.ValuesModeInvariant hasKeyfunc input`. Use the
`initialMergeState` transport theorem owned by `sortslice` safety, then carry
the invariant through the initial reverse, `count_run`, `binarysort`,
`found_new_run` (and its `merge_at` calls), the pending push, final collapse,
and final reverse. In parallel, carry the equation
`state.a.hasValues = initialized.a.hasValues = hasKeyfunc` through every scan
iteration and helper result. This equation must use the initializer projection
lemma and the explicit helper frame lemmas; it cannot be inferred from
`ValuesModeInvariant`, which is vacuous on an empty slice. The pending push,
reversal, and cleanup preserve the mode metadata directly.

In the same induction, establish an active temporary-storage package at
`initialMergeState`: `TempStorageInv state.a state.alloced`, `state.a.Live`, and
the logical-capacity consequence for the live backing. Carry the invariant and
liveness through every active scan state, through `found_new_run` and final
collapse, and into every `merge_at` call. The helper postconditions return the
same package for the next iteration. Only `finishListSort?` leaves the active
phase: apply the `merge_freemem` preservation theorem there and retain the
representation invariant and unchanged mode metadata, but do not claim that
heap-backed storage is still live after cleanup. The top-level execution
certificate must retain these active-state and final-cleanup facts so the later
trace-liveness and aggregate merge-memory nodes are corollaries of this actual
execution, not alternative reachability relations. It must likewise retain the
ordered helper-trace decomposition and each helper post's
`tempPayloadAccessesLive` field; the later liveness node composes those facts for
the complete trace rather than manufacturing a second evaluator.

For the public entry point, the proof uses the already-formalized proof-carrying
`listSort?` wrapper: its `ListSortInput.unkeyed`, `ListSortInput.unkeyedAs`,
and `ListSortInput.keyed` smart constructors establish the premise from arrays
by construction. The public adequacy result is stated for that wrapper and has
no free values-mode assumption.

Assemble the local traced evaluators here into raw `listSortImplTraced?`,
including the unconditional traced push and exact top-level fuel events. Its
erasure theorem
`(listSortImplTraced? ...).erase = listSortImpl? ...` must hold on the entire
raw input domain, without a values-mode premise; only the raw adequacy and
safety theorems take `hMode`. Then define the public wrapper
`listSortTraced? lt reverse input := listSortImplTraced? lt reverse
input.hasKeyfunc input.slice` over `ListSortInput`, and prove exact erasure to
`listSort?`. Thus the public trace is produced by the reviewed control flow
rather than attached afterward, and forgetting instrumentation recovers
precisely the validated public transcription.

## Merge-memory lifecycle export

The completed raw safety post now exposes the exact
`MergeMemoryLifecycle` on the actual `listSortImplTraced?` trace and the final
physical bound as public fields at
`Code/Assembly/ListSortTermination.lean:491` and
`Code/Assembly/ListSortTermination.lean:504`. The validated-input
post exposes the same two facts for `listSortTraced?` at
`Code/Assembly/ListSortTermination.lean:514` and
`Code/Assembly/ListSortTermination.lean:526`. They are
produced by `listSortImplTraced_safe` and `listSortTraced_safe`, whose exact
premises are stated at `Code/Assembly/ListSortTermination.lean:2092`
and `Code/Assembly/ListSortTermination.lean:2101`.

Within the induction, the private execution post carries three separate facts:
every recorded call is semantically valid, every recorded call is physically
bounded, and the literal event list is a continuous calls-plus-cleanup tail
(`Code/Assembly/ListSortTermination.lean:537`,
`Code/Assembly/ListSortTermination.lean:538`, and
`Code/Assembly/ListSortTermination.lean:539`).
The final top-level proof prefixes that real tail by the concrete initialized
snapshot using `mergeMemoryLifecycle_prepend_initial`; the invocation is at
`Code/Assembly/ListSortTermination.lean:1955`. This is proof-body
evidence for how the public lifecycle field is assembled; the exported field
and public theorem above are the theorem-level consumer boundary.

## Loop-invariant consumer diff

The per-iteration invariant consumed by the top-level induction is
`ListSortScanInvariant`. Its post-`found_new_run` reconstruction is implemented
by the private assembly lemma `listSortScanInvariant_after_push`, with the
following complete field accounting:

- `listlen`, `basekeys`, the data extent, the comparator, and the three
  adaptive-minrun fields come from `FoundNewRunSafetyPost.stableFrame`;
- the next cursor and `scanned + remaining = inputSize` partition follow from
  the consumed run length and the unconditional push;
- `PendingLayout` and `PoweredPrefix` come from
  `FoundNewRunSafetyPost.readyToPush` through
  `pushPendingRun_preserves_policy`;
- `TempStorageInv`, live backing, values mode, and the concrete `hasValues`
  equation come directly from the corresponding `FoundNewRunSafetyPost`
  fields and are framed by the push; and
- the next adaptive-minrun assertion uses the stable `listlen`/`mr_*` fields
  together with the already-established minrun step fact.

No field was added to the approved `FoundNewRunSafetyPost` contract while
performing this assembly. Trace fuel, ordinary-access bounds, temporary-payload
liveness, and the helper's empty push trace are composed separately with the
real unconditional push event.

## Depends on

- [list_sort_impl](../../transcription/list-sort-impl.md)
- [Array-access trace model](access-trace.md)
- [Merge-memory event validity and continuous-segment support](merge-memory-event-validity.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [sortslice primitive safety](sortslice-safe.md)

## Proof depends on

- [count_run safety](count-run-safe.md)
- [binarysort safety](binarysort-safe.md)
- [Slice-reversal safety](reverse-slice-safe.md)
- [`merge_init` establishes temporary-storage validity](merge-init-storage-valid.md)
- [`merge_freemem` preserves temporary-storage validity](merge-freemem-storage-valid.md)
- [found_new_run safety](found-new-run-safe.md)
- [merge_force_collapse safety](merge-force-collapse-safe.md)
- [Pushing the new run restores the steady-state invariant](../../policy/push-run-preservation.md)
- [powerloop terminating-result characterization](../../bit-equivalence/powerloop-result.md)
- [Unconditional adaptive-minrun output band](../../bit-equivalence/minrun-output-range.md)

## Sources

- [Safety theorem contract](../../../sources/toplevel-theorems.md#comparator-independent-safety)

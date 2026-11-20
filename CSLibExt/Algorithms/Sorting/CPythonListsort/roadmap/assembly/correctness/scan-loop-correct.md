---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listSortScan_complete_correct
---

# Complete scan and final-collapse correctness

`listSortScan_complete_correct` closes the induction left open by the approved
one-step theorem.  From `ListSortScanCorrectnessInvariant` and the same
`remaining ≤ fuel` adequacy relation used by the safety assembly, it returns a
real terminal scan state, the result of that state's actual
`mergeForceCollapse?` call, and the successful `listSortScan?` result
(`Code/Correctness/ScanLoopCorrectness.lean:264`).  The theorem is
parameterized by an arbitrary `reverse` flag; it does not silently specialize
the principal composition theorem to the forward path.

The public `ListSortScanCollapseCorrectnessPost` retains all three boundaries
in view (`Code/Correctness/ScanLoopCorrectness.lean:29`; definition,
not a proof pin).  In particular, it records:

- the combined invariant at the real terminal call with `scanned = inputSize`
  and `remaining = 0`;
- the complete `MergeForceCollapseCorrectnessPost` for the pre-finish
  `collapsed` state and the exact raw equation
  `mergeForceCollapse? terminal = some collapsed`;
- the exact equation from the initial `listSortScan?` call to
  `finishListSort? collapsed.state reverse inputSize 0 false` and successful
  result equations for both sides;
- return code zero and fuel non-exhaustion; and
- the singleton final run's exact bounds, shared `Sorted` predicate,
  `StableOccurrencePermutation`, and the pre-finish whole-entry snapshot.

Those fields are inhabited simultaneously by
`listSortScan_complete_correct`, not inferred from successful compilation.  Its
theorem-level pin is
`Code/Correctness/ScanLoopCorrectness.lean:264`.
The proof-body composition invokes the public step theorem at
`Code/Correctness/ScanLoopCorrectness.lean:290`, derives the recursive
fuel bound from the step's positive consumption, and invokes the actual final
collapse theorem at
`Code/Correctness/ScanLoopCorrectness.lean:218`.  Result existence is
tied to the synchronized traced evaluator through `listSortScanTraced_safe` at
`Code/Correctness/ScanLoopCorrectness.lean:235`; this is proof-body
evidence, while the public raw result equation is theorem-pinned by the main
theorem at `Code/Correctness/ScanLoopCorrectness.lean:264` and its
post.

`listSortScanCorrectnessInvariant_initial` proves that every validated
occurrence-tagged input of size at least two and at most `PY_LIST_MAX`
establishes the exact combined invariant at the first scan call
(`Code/Correctness/ScanLoopCorrectness.lean:127`).  Thus the principal
theorem's invariant premise has a public top-level producer rather than being a
locally assumed reachability condition.

Forward cleanup is exported separately by `listSortScan_forward_correct`
(`Code/Correctness/ScanLoopCorrectness.lean:315`).  It specializes
the principal theorem to `reverse = false`, proves that the returned state is
exactly `mergeFreemem collapsed.state`, and transports the whole-entry snapshot
through that cleanup.  Reverse-mode correctness instead consumes the
principal theorem's pre-finish state before proving the final reversal.

## Review pins

- `listSortScan_complete_correct` exports the real recursive evaluator equation,
  successful result existence, final-collapse result, and semantic post in one
  certificate
  (`Code/Correctness/ScanLoopCorrectness.lean:264`).
- `ListSortScanCollapseCorrectnessPost.wholeDataCorrect` derives full-array
  sortedness and occurrence stability from the terminal singleton run rather
  than assuming that the run covers the array
  (`Code/Correctness/ScanLoopCorrectness.lean:70`).
- `listSortScanCorrectnessInvariant_initial` supplies the complete scan
  invariant from a validated input, including storage liveness and the keyed
  values-mode relation; neither is left as a top-level premise
  (`Code/Correctness/ScanLoopCorrectness.lean:127`).

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Pending-run correctness invariant](pending-run-correctness.md)
- [Unscanned suffix matches the input snapshot](scan-remainder-matches.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [Top-level scan preserves pending-run correctness](scan-step-correct.md)
- [Final collapse produces one correct run](force-collapse-correct.md)
- [list_sort_impl](../../transcription/list-sort-impl.md)

## Proof depends on

- [`list_sort_impl` fuel adequacy and scan invariant](../safety/termination.md)

## Sources

- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
- [Functional-correctness theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)

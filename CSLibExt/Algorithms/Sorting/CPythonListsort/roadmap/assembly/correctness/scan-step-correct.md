---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listSortScan_step_correct
---

# Top-level scan preserves pending-run correctness

`listSortScan_step_correct` is the induction step for one nonterminal iteration
of the real `listSortScan?` evaluator.  Its only explicit mathematical premise
besides `0 < remaining` is a Boolean strict weak order; all machine and
semantic state assumptions arrive through `ListSortScanCorrectnessInvariant`.
It returns a positive `consumed ≤ remaining`, the exact next state, and a
`ListSortScanStepCorrectnessPost`
(`Correctness/ScanStepCorrectness.lean:765`).

`ListSortScanCorrectnessInvariant` is definitionally the reviewed
`ListSortScanInvariant` plus `PendingRunsCorrect`,
`ScanRemainderEntriesMatch`, and `EntrySnapshotPermutation`
(`Correctness/ScanStepCorrectness.lean:31`; definition, not a
proof pin).  Thus powered-prefix, storage, liveness, values-mode,
adaptive-minrun, and cursor facts remain owned by the safety invariant rather
than being silently re-assumed by the correctness layer.

The post records four observable facts: the consumed length is positive and in
range; all entries outside the enlarged consumed prefix are framed; the real
evaluator is exactly equal to its recursive call with advanced cursor and
reduced remainder; and the same combined invariant holds at that recursive
call.  These are the definition fields at
`Correctness/ScanStepCorrectness.lean:44`; their simultaneous
inhabitance is theorem-pinned by `listSortScan_step_correct` at
`Correctness/ScanStepCorrectness.lean:765`.

As proof-body evidence, the generic composition uses the local `count_run` and
`binarysort` posts to obtain a sorted, occurrence-stable new run, invokes its
abstract `foundCorrect` provider, and then performs the transcription's
unconditional pending-stack push
(`Correctness/ScanStepCorrectness.lean:170`, `:335`, `:715`,
and `:721`). The public theorem instantiates that provider with
`foundNewRun_correct` at
`Correctness/ScanStepCorrectness.lean:779`. Independently, the
public `found_new_run` theorem preserves
pending-run correctness, the entry snapshot, comparator binding, and the
consumed-prefix frame across every merge it takes
(`Correctness/FoundNewRunCorrectness.lean:445`).  The semantic
push itself is exported as `PendingRunsCorrect.pushPendingRun`
(`Correctness/ScanStepSupport.lean:173`).

The theorem quantifies the evaluator's `reverse` flag because one nonterminal
iteration merely passes it to the recursive call.  Its semantic invariant is
still the forward canonical-occurrence invariant, so this theorem is not
directly applicable after reverse mode's initial whole-slice reversal.  The
separate [reverse-oriented scan transport](reverse-scan-transport.md) node
owns the mirrored-origin relabeling and evaluator-equivariance argument; that
application boundary is deliberately not claimed here.

## Review pins

- A short descending natural run of length two is extended and stably sorted
  across a forced four-entry range; keyed payloads remain paired and both
  outside sentinels are unchanged:
  `listSortScan_short_run_extension_regression`
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/ScanStepCorrectness.lean:67`).
- A natural run of length forty, above the adaptive target thirty-two, takes
  the no-extension path, is pushed at its own length, and collapses with the
  preceding run to the unchanged sixty-four-entry range. This is an asserting
  `IO Unit` runtime regression in the test library:
  `listSortScan_long_run_no_extension_regression`
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/ScanStepCorrectness.lean:92`).
- The strict-power-merge-before-push path is observable: the trace records push
  depth two rather than the depth three a direct push would produce, and the
  final data is sorted. This is an asserting `IO Unit` runtime regression in
  the test library:
  `listSortScan_policy_merge_then_push_regression`
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/ScanStepCorrectness.lean:137`).
- At the lower layer, the taken strict-power branch observably merges the two
  one-element runs, changes `2,1` to `1,2`, shrinks the pending stack, and
  writes the incoming power on the combined run. This is an asserting
  `IO Unit` runtime regression in the test library:
  `foundNewRunLoop_taken_merge_regression`
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/FoundNewRunCorrectness.lean:44`).

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Pending-run correctness invariant](pending-run-correctness.md)
- [Unscanned suffix matches the input snapshot](scan-remainder-matches.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [list_sort_impl](../../transcription/list-sort-impl.md)
- [`list_sort_impl` fuel adequacy and scan invariant](../safety/termination.md)

## Proof depends on

- [count_run produces a stable sorted run](count-run-correct.md)
- [binarysort preserves and extends stable sortedness](binarysort-correct.md)
- [merge_at stable correctness](merge-correct.md)
- [`found_new_run` preserves policy invariants](../../policy/found-new-run-preservation.md)
- [`found_new_run` safety](../safety/found-new-run-safe.md)
- [Pushing the new run restores the steady-state invariant](../../policy/push-run-preservation.md)
- [Unconditional adaptive-minrun output band](../../bit-equivalence/minrun-output-range.md)

## Sources

- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
- [Verbatim `found_new_run`](../../../sources/listobject-excerpts.md#found-new-run)

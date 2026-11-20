---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeForceCollapse_correct
---

# Final collapse produces one correct run

`mergeForceCollapse_correct` proves correctness of the real fuel-bounded final
collapse.  From a Boolean strict weak order, the list-size bound, a nonempty
pending stack, `PendingRunsCorrect`, an input `EntrySnapshotPermutation`,
`TempStorageInv`, live temporary backing, synchronized values mode, and
comparator binding, it returns a result satisfying
`MergeForceCollapseCorrectnessPost`
(`Code/Correctness/MergeForceCollapseCorrectness.lean:158`).

The post embeds the traced `MergeForceCollapseSafetyPost` and preserves
`PendingRunsCorrect`, the whole-entry snapshot, comparator binding, and the
outside-consumed-prefix frame.  Those fields are the definition at
`Code/Correctness/MergeForceCollapseCorrectness.lean:21`, not an
independent proof pin.  The recursive proof body delegates every taken merge
to `mergeAt_correct`; that is a proof-body fact rather than a separate public
pin.

The exported `MergeForceCollapseCorrectnessPost.finalRunCorrect` theorem turns
that compositional post into the final consumer-facing result: there is one
pending run, it begins at the original `basekeys`, ends at
`basekeys + scanned`, is sorted under `occurrenceComparator lt`, and is a
`StableOccurrencePermutation` of the canonical consumed input segment
(`Code/Correctness/MergeForceCollapseCorrectness.lean:196`).

## Review pins

- The complete final-collapse evaluator returns the traced semantic post under
  the premises above: `mergeForceCollapse_correct`
  (`Code/Correctness/MergeForceCollapseCorrectness.lean:158`).
- A singleton pending stack is observably a successful no-op with the input
  state returned unchanged:
  `mergeForceCollapseTraced_singleton_noop`
  (`Code/Correctness/MergeForceCollapseCorrectness.lean:227`).
- A concrete three-run execution of the real evaluator returns a single
  three-element run while retaining equal-key absolute-origin order and all
  paired payloads. This is a compiler-checked `native_decide` witness and is
  not consumed by the kernel-checked correctness theorem:
  `mergeForceCollapse_threeRun_equalKey_payload_regression`
  (`Code/Correctness/MergeForceCollapseCorrectness.lean:298`).

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Pending-run correctness invariant](pending-run-correctness.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [merge_force_collapse](../../transcription/merge-force-collapse.md)
- [merge_force_collapse safety](../safety/merge-force-collapse-safe.md)

## Proof depends on

- [merge_at stable correctness](merge-correct.md)
- [merge_force_collapse preserves layout](../../policy/force-collapse-preservation.md)

## Sources

- [Verbatim `merge_force_collapse`](../../../sources/listobject-excerpts.md#merge-force-collapse)

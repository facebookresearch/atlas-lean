---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeAt_correct
---

# `merge_at` stable correctness

`mergeAt_correct` is the end-to-end theorem for the real `merge_at` evaluator.
Its premises are exactly a Boolean strict weak order, `PendingRunsCorrect`, an
input `EntrySnapshotPermutation`, comparator binding, the `PY_LIST_MAX` bound,
one of CPython's two admitted stack positions, `TempStorageInv`, live temporary
backing, and synchronized values mode.  It returns a result satisfying
`MergeAtCorrectnessPost`
(`Code/Correctness/MergeAtCorrectness.lean:1752`).

`MergeAtCorrectnessPost` embeds the traced `MergeAtSafetyPost`, preserves
`PendingRunsCorrect` and the whole-entry snapshot, re-exports comparator
binding, and frames every cell outside the already-consumed prefix.  Its
fields are a definition at
`Code/Correctness/MergeAtCorrectness.lean:86`, not a separate proof
pin.

For the selected adjacent pair, `MergeAtSelectedPairCorrectness` records the
two selected stack entries and their exact splice, then states that the entire
pre-trimming union—not only the middle range passed to `merge_lo` or
`merge_hi`—equals `mergeAtTargetEntries`.  It also exports sortedness,
occurrence stability, a whole-entry permutation, and
`SortSlice.EqualOutsideRange` for that union.  This certificate is defined at
`Code/Correctness/MergeAtCorrectness.lean:51`; its target is
definitionally the forward left-biased `stableEntryMerge` of the two complete
runs at `Code/Correctness/MergeAtCorrectness.lean:40`.

The public theorem has no extra call-site `MergeSemanticPre`, trimming, or
canonical-stability premise: those obligations are discharged inside the
composition from `PendingRunsCorrect` and the two verified gallops.  This is a
fact about the public theorem's signature at
`Code/Correctness/MergeAtCorrectness.lean:1752`; the internal
derivation is a proof-body fact, not an additional public theorem.

## Review pins

- The complete evaluator returns the global post above under only the stated
  scan, storage, position, and order premises: `mergeAt_correct`
  (`Code/Correctness/MergeAtCorrectness.lean:1752`).
- Under the strict weak order and sorted-run premises, the defensive
  post-second-gallop `nb = 0` branch is impossible:
  `mergeAt_secondTrimZero_impossible`
  (`Code/Correctness/MergeAtCorrectness.lean:699`).
- Concrete executions observably reach the successful early-left-exhaustion,
  nonempty `merge_lo`, and nonempty `merge_hi` preparation outcomes
  (`Code/Correctness/MergeAtCorrectness.lean:1900`,
  `Code/Correctness/MergeAtCorrectness.lean:1911`, and
  `Code/Correctness/MergeAtCorrectness.lean:1920`).
- The third-last stack-position fixture pins the pending-stack slide as well as
  successful completion. This named executable witness is compiler-checked via
  `native_decide`, not a kernel-checked premise of `mergeAt_correct`
  (`Code/Correctness/MergeAtCorrectness.lean:1929`).
- Outside the strict-order theorem's domain, a deliberately inconsistent
  comparator observably reaches the defensive second-trim-zero success arm;
  this anti-vacuity regression does not weaken the theorem's order premise
  (`Code/Correctness/MergeAtCorrectness.lean:1944`).

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Pending-run correctness invariant](pending-run-correctness.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [merge_at](../../transcription/merge-at.md)
- [merge_at safety](../safety/merge-at-safe.md)

## Proof depends on

- [gallop_left partition specification](gallop-correct.md)
- [gallop_right partition specification](gallop-right-correct.md)
- [merge_lo stable correctness](merge-lo-correct.md)
- [merge_hi stable correctness](merge-hi-correct.md)
- [merge_at preserves pending layout](../../policy/merge-at-preservation.md)

## Sources

- [CPython merge algorithms](../../../sources/listsort.md#merge-algorithms)
- [Verbatim `merge_at`](../../../sources/listobject-excerpts.md#merge-at)

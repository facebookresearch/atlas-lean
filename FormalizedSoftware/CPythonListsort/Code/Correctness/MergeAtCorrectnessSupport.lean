/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.EntrySnapshotPermutation
import Code.Correctness.StableMerge
import Code.Policy.MergeAtPreservation

/-!
# Correctness support for `merge_at`

This module contains only the list algebra needed to lift one correct merge of
two adjacent pending runs to the global pending-run and input-snapshot
invariants.  Evaluator control flow remains in the eventual `merge_at`
correctness theorem.
-/

namespace CPythonListsort

universe u v

/-- Occurrence keys contributed by an explicitly supplied list of pending
runs.  Unlike `pendingOccurrenceKeys`, this view is useful before and after an
adjacent pair is replaced in the pending array. -/
def pendingOccurrenceKeysOf
    (state : MergeState (Occurrence α) ν) (runs : List PendingRun) :
    List (Occurrence α) :=
  runs.flatMap fun run => (pendingRunOccurrenceKeys state run).toList

@[simp]
theorem pendingOccurrenceKeysOf_nil
    (state : MergeState (Occurrence α) ν) :
    pendingOccurrenceKeysOf state [] = [] := by
  rfl

@[simp]
theorem pendingOccurrenceKeysOf_cons
    (state : MergeState (Occurrence α) ν) (run : PendingRun)
    (runs : List PendingRun) :
    pendingOccurrenceKeysOf state (run :: runs) =
      (pendingRunOccurrenceKeys state run).toList ++
        pendingOccurrenceKeysOf state runs := by
  rfl

@[simp]
theorem pendingOccurrenceKeysOf_append
    (state : MergeState (Occurrence α) ν) (left right : List PendingRun) :
    pendingOccurrenceKeysOf state (left ++ right) =
      pendingOccurrenceKeysOf state left ++
        pendingOccurrenceKeysOf state right := by
  simp [pendingOccurrenceKeysOf]

/-- The full pending-key view is the explicit-run view at the current pending
array. -/
theorem pendingOccurrenceKeys_eq_of_pending
    (state : MergeState (Occurrence α) ν) :
    pendingOccurrenceKeys state =
      pendingOccurrenceKeysOf state state.pending.toList := by
  rfl

/-- Pointwise equality of every run view lifts to equality of the flattened
pending occurrence view. -/
theorem pendingOccurrenceKeysOf_congr
    {before after : MergeState (Occurrence α) ν}
    {runs : List PendingRun}
    (hkeys : ∀ run ∈ runs,
      pendingRunOccurrenceKeys before run =
        pendingRunOccurrenceKeys after run) :
    pendingOccurrenceKeysOf before runs =
      pendingOccurrenceKeysOf after runs := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      simp only [pendingOccurrenceKeysOf_cons]
      rw [hkeys run (by simp), ih]
      intro tail htail
      exact hkeys tail (by simp [htail])

/-- Exact flattened-key decomposition around two adjacent pending runs. -/
theorem pendingOccurrenceKeys_pair_decomposition
    {state : MergeState (Occurrence α) ν}
    {before after : List PendingRun} {left right : PendingRun}
    (hsplit : state.pending.toList = before ++ left :: right :: after) :
    pendingOccurrenceKeys state =
      pendingOccurrenceKeysOf state before ++
        (pendingRunOccurrenceKeys state left).toList ++
        (pendingRunOccurrenceKeys state right).toList ++
        pendingOccurrenceKeysOf state after := by
  rw [pendingOccurrenceKeys_eq_of_pending, hsplit]
  simp only [pendingOccurrenceKeysOf_append,
    pendingOccurrenceKeysOf_cons, List.append_assoc]

/-- Exact flattened-key decomposition around one pending run. -/
theorem pendingOccurrenceKeys_single_decomposition
    {state : MergeState (Occurrence α) ν}
    {before after : List PendingRun} {run : PendingRun}
    (hsplit : state.pending.toList = before ++ run :: after) :
    pendingOccurrenceKeys state =
      pendingOccurrenceKeysOf state before ++
        (pendingRunOccurrenceKeys state run).toList ++
        pendingOccurrenceKeysOf state after := by
  rw [pendingOccurrenceKeys_eq_of_pending, hsplit]
  simp only [pendingOccurrenceKeysOf_append,
    pendingOccurrenceKeysOf_cons, List.append_assoc]

/-- A semantic frame identifies the occurrence keys of every pending run whose
range is disjoint from the modified range. -/
theorem pendingRunOccurrenceKeys_eq_of_equalOutsideRange
    {before after : MergeState (Occurrence α) ν}
    {start count : Nat} (run : PendingRun)
    (frame : SortSlice.EqualOutsideRange before.data after.data start count)
    (disjoint : run.endIndex ≤ start ∨ start + count ≤ run.base) :
    pendingRunOccurrenceKeys before run =
      pendingRunOccurrenceKeys after run := by
  rw [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
    pendingRunOccurrenceKeys_eq_sortSliceRangeKeys]
  exact frame.keys_eq_of_disjoint run.base run.len.toNat (by
    simpa only [PendingRun.endIndex] using disjoint)

/-- Replacing one contiguous segment by a permutation with its own pairwise
relation preserves the pairwise relation on the complete list. -/
theorem pairwise_replaceSegmentPerm
    {R : α → α → Prop}
    {pre original replacement suffix : List α}
    (whole : (pre ++ original ++ suffix).Pairwise R)
    (replacementPairwise : replacement.Pairwise R)
    (replacementPerm : replacement.Perm original) :
    (pre ++ replacement ++ suffix).Pairwise R := by
  rcases List.pairwise_append.mp whole with
    ⟨prefixOriginal, suffixPairwise, prefixOriginalToSuffix⟩
  rcases List.pairwise_append.mp prefixOriginal with
    ⟨prefixPairwise, _originalPairwise, prefixToOriginal⟩
  have prefixReplacement : (pre ++ replacement).Pairwise R := by
    apply List.pairwise_append.mpr
    refine ⟨prefixPairwise, replacementPairwise, ?_⟩
    intro earlier hearlier later hlater
    exact prefixToOriginal earlier hearlier later
      (replacementPerm.mem_iff.mp hlater)
  apply List.pairwise_append.mpr
  refine ⟨prefixReplacement, suffixPairwise, ?_⟩
  intro earlier hearlier later hlater
  rcases List.mem_append.mp hearlier with hearlier | hearlier
  · exact prefixOriginalToSuffix earlier
      (List.mem_append_left original hearlier) later hlater
  · exact prefixOriginalToSuffix earlier
      (List.mem_append_right pre
        (replacementPerm.mem_iff.mp hearlier)) later hlater

namespace StableOccurrencePermutation

/-- A stable permutation of a contiguous segment may replace that segment in
a globally stable occurrence permutation. -/
theorem replaceSegment
    {lt : BoolComparator α} {canonical : List (Occurrence α)}
    {pre original replacement suffix : List (Occurrence α)}
    (whole : StableOccurrencePermutation lt canonical
      (pre ++ original ++ suffix))
    (segment : StableOccurrencePermutation lt original replacement) :
    StableOccurrencePermutation lt canonical
      (pre ++ replacement ++ suffix) := by
  refine ⟨?_, ?_⟩
  · exact ((segment.1.append_left pre).append_right suffix).trans whole.1
  · exact pairwise_replaceSegmentPerm whole.2 segment.2 segment.1

end StableOccurrencePermutation

namespace PendingRunsCorrect

/-- Replace two adjacent correct pending runs by one correct stable merge.

The structural postcondition is supplied directly by
`mergeAt_preserves_pendingLayout`.  The two unchanged-run premises are the
precise frame obligations: they can be discharged with
`pendingRunOccurrenceKeys_eq_of_equalOutsideRange`. -/
theorem replaceAdjacent
    {lt : BoolComparator α} {input : Array α}
    {beforeState afterState : MergeState (Occurrence α) ν}
    {scanned : Nat} {pre suffix : List PendingRun}
    {left right merged : PendingRun}
    (correct : PendingRunsCorrect lt input beforeState scanned)
    (layout : PendingLayout afterState scanned)
    (basekeys : afterState.basekeys = beforeState.basekeys)
    (beforePending : beforeState.pending.toList =
      pre ++ left :: right :: suffix)
    (afterPending : afterState.pending.toList =
      pre ++ merged :: suffix)
    (prefixKeys : ∀ run ∈ pre,
      pendingRunOccurrenceKeys beforeState run =
        pendingRunOccurrenceKeys afterState run)
    (suffixKeys : ∀ run ∈ suffix,
      pendingRunOccurrenceKeys beforeState run =
        pendingRunOccurrenceKeys afterState run)
    (mergedSorted :
      Sorted (occurrenceComparator lt)
        (pendingRunOccurrenceKeys afterState merged))
    (mergedStable : StableOccurrencePermutation lt
      ((pendingRunOccurrenceKeys beforeState left).toList ++
        (pendingRunOccurrenceKeys beforeState right).toList)
      (pendingRunOccurrenceKeys afterState merged).toList) :
    PendingRunsCorrect lt input afterState scanned := by
  have prefixFlat := pendingOccurrenceKeysOf_congr prefixKeys
  have suffixFlat := pendingOccurrenceKeysOf_congr suffixKeys
  refine ⟨layout, ?_, ?_⟩
  · intro run hrun
    rw [afterPending] at hrun
    simp only [List.mem_append, List.mem_cons] at hrun
    rcases hrun with hprefix | rfl | hsuffix
    · rw [← prefixKeys run hprefix]
      apply correct.runSorted run
      rw [beforePending]
      simp [hprefix]
    · exact mergedSorted
    · rw [← suffixKeys run hsuffix]
      apply correct.runSorted run
      rw [beforePending]
      simp [hsuffix]
  · have oldStable := correct.stableOccurrencePermutation
    have oldDecomposition :=
      pendingOccurrenceKeys_pair_decomposition beforePending
    have newDecomposition :=
      pendingOccurrenceKeys_single_decomposition afterPending
    rw [oldDecomposition] at oldStable
    rw [newDecomposition, basekeys, ← prefixFlat, ← suffixFlat]
    have oldStable' : StableOccurrencePermutation lt
        (canonicalOccurrenceSegment input beforeState.basekeys scanned)
        (pendingOccurrenceKeysOf beforeState pre ++
          ((pendingRunOccurrenceKeys beforeState left).toList ++
            (pendingRunOccurrenceKeys beforeState right).toList) ++
          pendingOccurrenceKeysOf beforeState suffix) := by
      simpa only [List.append_assoc] using oldStable
    exact oldStable'.replaceSegment mergedStable

end PendingRunsCorrect

namespace EntrySnapshotPermutation

/-- The exact snapshot/frame lifting shape used after either concrete merge
implementation has established a local whole-entry permutation. -/
theorem preserve_mergeRange
    {source : SortSlice κ ν}
    {before after : SortSlice (Occurrence κ) ν}
    {start count : Nat}
    (snapshot : EntrySnapshotPermutation source before)
    (frame : SortSlice.EqualOutsideRange before after start count)
    (stop : start + count ≤ before.entries.size)
    (rangePerm :
      (sortSliceRangeEntries after start count).toList.Perm
        (sortSliceRangeEntries before start count).toList) :
    EntrySnapshotPermutation source after :=
  snapshot.preserve_local frame stop rangePerm

end EntrySnapshotPermutation

end CPythonListsort

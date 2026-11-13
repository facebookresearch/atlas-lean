/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.BinarysortCorrectness
import Code.Correctness.CountRunCorrectness
import Code.Correctness.EntrySnapshotPermutation
import Code.Correctness.ScanCorrectnessSupport
import Code.Policy.PushRunPreservation

/-!
# Semantic bridges for one forward scan step

These lemmas connect the already-public natural-run and binary-insertion
certificates to the scan invariant.  They contain no second implementation of
the scan: every update is the range frame or pending-stack push exported by
the transcribed operation's correctness theorem.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- A key range of sum length splits at the first summand. -/
theorem sortSliceRangeKeys_toList_add
    (slice : SortSlice alpha nu) (start leftCount rightCount : Nat) :
    (sortSliceRangeKeys slice start (leftCount + rightCount)).toList =
      (sortSliceRangeKeys slice start leftCount).toList ++
        (sortSliceRangeKeys slice (start + leftCount) rightCount).toList := by
  simp only [sortSliceRangeKeys_toList, List.take_add, List.drop_drop,
    List.map_append]

namespace CountRunCorrectnessPost

/-- The count-run stability postcondition is relative to the exact source
range read by `count_run`.  Whole-entry remainder agreement identifies that
source range with the absolute-origin canonical segment used by the scan
invariant. -/
theorem stable_from_remainder
    {lt : BoolComparator alpha} {source : SortSlice alpha nu}
    {state : MergeState (Occurrence alpha) nu} {scanned : Nat}
    {base : Int} {nremaining : Nat}
    {result : CountRunResult (Occurrence alpha) nu}
    (post : CountRunCorrectnessPost lt state state.data base nremaining result)
    (remainder : ScanRemainderEntriesMatch source state scanned)
    (hbase : base.toNat = state.basekeys + scanned)
    (hresultRemaining : result.length ≤ state.listlen.toNat - scanned) :
    StableOccurrencePermutation lt
      (canonicalOccurrenceSegment
        (source.entries.map SortSliceEntry.key)
        (state.basekeys + scanned) result.length)
      (sortSliceRangeKeys result.slice
        (state.basekeys + scanned) result.length).toList := by
  have hsource := remainder.prefix_keys_eq hresultRemaining
  have hstable := post.stable
  rw [hbase] at hstable
  rw [hsource] at hstable
  exact hstable

/-- If `count_run` finds a prefix shorter than the forced minrun target, its
stable output prefix followed by the untouched source suffix is already a
stable permutation of the entire target range.  This is the exact stability
premise consumed by `binarysort_correct`; it works for every admitted forced
length, not only for a particular minrun formula. -/
theorem stable_for_forced_range
    {lt : BoolComparator alpha} {source : SortSlice alpha nu}
    {state : MergeState (Occurrence alpha) nu} {scanned force : Nat}
    {base : Int} {nremaining : Nat}
    {result : CountRunResult (Occurrence alpha) nu}
    (post : CountRunCorrectnessPost lt state state.data base nremaining result)
    (remainder : ScanRemainderEntriesMatch source state scanned)
    (hbase : base.toNat = state.basekeys + scanned)
    (hrunForce : result.length ≤ force)
    (hforceRemaining : force ≤ state.listlen.toNat - scanned) :
    StableOccurrencePermutation lt
      (canonicalOccurrenceSegment
        (source.entries.map SortSliceEntry.key)
        (state.basekeys + scanned) force)
      (sortSliceRangeKeys result.slice
        (state.basekeys + scanned) force).toList := by
  let input := source.entries.map SortSliceEntry.key
  let start := state.basekeys + scanned
  have hprefix : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input start result.length)
      (sortSliceRangeKeys result.slice start result.length).toList := by
    exact post.stable_from_remainder remainder hbase
      (le_trans hrunForce hforceRemaining)
  have hbeforeWhole :
      (sortSliceRangeKeys state.data start force).toList =
        canonicalOccurrenceSegment input start force := by
    exact remainder.prefix_keys_eq hforceRemaining
  have hbeforeSuffix :
      (sortSliceRangeKeys state.data (start + result.length)
        (force - result.length)).toList =
        canonicalOccurrenceSegment input (start + result.length)
          (force - result.length) := by
    have hdropped := congrArg (List.drop result.length) hbeforeWhole
    rw [sortSliceRangeKeys_toList_drop,
      ScanRemainderMatches.canonicalOccurrenceSegment_drop] at hdropped
    exact hdropped
  have hafterSuffix :
      (sortSliceRangeKeys result.slice (start + result.length)
        (force - result.length)).toList =
        canonicalOccurrenceSegment input (start + result.length)
          (force - result.length) := by
    have hpostFrame := post.frame
    rw [hbase] at hpostFrame
    have hframe := hpostFrame.keys_eq_of_disjoint
      (start + result.length) (force - result.length) (Or.inr le_rfl)
    rw [← hframe]
    exact hbeforeSuffix
  have hsuffix : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input (start + result.length)
        (force - result.length))
      (sortSliceRangeKeys result.slice (start + result.length)
        (force - result.length)).toList := by
    rw [hafterSuffix]
    exact canonicalOccurrenceSegment_countRunCanonical lt input
      (start + result.length) (force - result.length)
  have happended := stableOccurrencePermutation_append_adjacent hprefix hsuffix
  have hforce : result.length + (force - result.length) = force := by omega
  have hsplit := sortSliceRangeKeys_toList_add result.slice start
    result.length (force - result.length)
  rw [hforce] at hsplit happended
  rw [hsplit]
  exact happended

end CountRunCorrectnessPost

namespace EntrySnapshotPermutation

/-- Lift the whole-entry permutation and frame exported by `count_run` to the
persistent whole-input snapshot. -/
theorem preserve_countRun
    {lt : BoolComparator alpha} {source : SortSlice alpha nu}
    {state : MergeState (Occurrence alpha) nu}
    {base : Int} {nremaining : Nat}
    {result : CountRunResult (Occurrence alpha) nu}
    (snapshot : EntrySnapshotPermutation source state.data)
    (post : CountRunCorrectnessPost lt state state.data base nremaining result)
    (hstop : base.toNat + result.length ≤ state.data.entries.size) :
    EntrySnapshotPermutation source result.slice := by
  exact snapshot.preserve_local post.frame hstop post.entryPermutation

/-- Lift the whole-entry permutation and frame exported by `binarysort` to
the persistent whole-input snapshot. -/
theorem preserve_binarysort
    {lt : BoolComparator alpha} {source : SortSlice alpha nu}
    {canonical : List (Occurrence alpha)}
    {state : MergeState (Occurrence alpha) nu}
    {before : SortSlice (Occurrence alpha) nu}
    {base n ok : Nat} {result : BinarysortResult (Occurrence alpha) nu}
    (snapshot : EntrySnapshotPermutation source before)
    (post : BinarysortCorrectnessPost lt canonical state before base n ok result)
    (hstop : base + n ≤ before.entries.size) :
    EntrySnapshotPermutation source result.slice := by
  exact snapshot.preserve_local post.frame hstop post.rangeEntriesPerm

end EntrySnapshotPermutation

namespace PendingRunsCorrect

/-- The actual unconditional pending-stack push appends one newly formed
adjacent run to the semantic pending-run invariant.  `ReadyToPush` supplies
the structural layout transition; the two semantic premises are exactly the
sortedness and canonical stability certificates produced by run formation. -/
theorem pushPendingRun
    {lt : BoolComparator alpha} {input : Array alpha}
    {state : MergeState (Occurrence alpha) nu}
    {scanned : Nat} {newRun : PendingRun}
    (correct : PendingRunsCorrect lt input state scanned)
    (ready : ReadyToPush state scanned newRun)
    (newSorted : Sorted (occurrenceComparator lt)
      (pendingRunOccurrenceKeys state newRun))
    (newStable : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input (state.basekeys + scanned)
        newRun.len.toNat)
      (pendingRunOccurrenceKeys state newRun).toList) :
    PendingRunsCorrect lt input (CPythonListsort.pushPendingRun state newRun)
      (scanned + newRun.len.toNat) := by
  let pushed := CPythonListsort.pushPendingRun state newRun
  have hlayout : PendingLayout pushed (scanned + newRun.len.toNat) :=
    pushPendingRun_preserves_pendingLayout state scanned newRun ready
  have hpending : pushed.pending.toList =
      state.pending.toList ++ [newRun] := by
    simp [pushed, CPythonListsort.pushPendingRun]
  have hnewKeys : pendingRunOccurrenceKeys pushed newRun =
      pendingRunOccurrenceKeys state newRun := by
    rfl
  refine ⟨hlayout, ?_, ?_⟩
  · intro run hrun
    rw [hpending] at hrun
    rcases List.mem_append.mp hrun with hold | hnew
    · simpa [pendingRunOccurrenceKeys, pushed,
        CPythonListsort.pushPendingRun] using correct.runSorted run hold
    · simp only [List.mem_singleton] at hnew
      subst run
      rw [hnewKeys]
      exact newSorted
  · have hold := correct.stableOccurrencePermutation
    have happended := stableOccurrencePermutation_append_adjacent hold newStable
    change StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input pushed.basekeys
        (scanned + newRun.len.toNat))
      (pendingOccurrenceKeys pushed)
    have hbase : pushed.basekeys = state.basekeys := rfl
    rw [hbase]
    unfold pendingOccurrenceKeys
    rw [hpending]
    rw [List.flatMap_append]
    simp only [List.flatMap_singleton]
    simpa [pendingOccurrenceKeys, pushed, CPythonListsort.pushPendingRun,
      hnewKeys] using happended

end PendingRunsCorrect

end CPythonListsort

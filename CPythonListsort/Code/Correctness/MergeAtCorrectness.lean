/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.GallopCorrectness
import Code.Assembly.MergeAtSafety
import Code.Correctness.MergeAtCorrectnessSupport
import Code.Correctness.MergeHiCorrectness
import Code.Correctness.MergeLoCorrectness
import Code.Correctness.PendingRunCorrectness
import Code.Policy.MergeAtPreservation
import Code.Policy.MergeTopPowerPreservation

/-!
# Functional correctness of `merge_at`

This module lifts the exact trimmed-range specifications of `merge_lo` and
`merge_hi` to the complete adjacent pair selected by `merge_at`.  Its public
postcondition is deliberately phrased at the scan invariant boundary: the
actual traced evaluator succeeds, the selected union is the mathematical
left-biased stable merge, all pending runs remain correct, the persistent
whole-entry snapshot is preserved, and no entry outside the consumed prefix
changes.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Whole entries of the left run selected by `merge_at`, before trimming. -/
def mergeAtLeftEntries (pre : MergeState (Occurrence alpha) nu)
    (left : PendingRun) : List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries pre.data left.base left.len.toNat).toList

/-- Whole entries of the right run selected by `merge_at`, before trimming. -/
def mergeAtRightEntries (pre : MergeState (Occurrence alpha) nu)
    (right : PendingRun) : List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries pre.data right.base right.len.toNat).toList

/-- The source-faithful full-union target: an ordinary forward, left-biased
stable merge of the two complete adjacent runs. -/
def mergeAtTargetEntries (lt : BoolComparator alpha)
    (pre : MergeState (Occurrence alpha) nu) (left right : PendingRun) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  stableEntryMerge lt (mergeAtLeftEntries pre left)
    (mergeAtRightEntries pre right)

/-- Functional certificate for the exact pair selected by `merge_at`.

`exactRange` covers the complete pre-trimming union, not merely the smaller
middle range passed to `merge_lo` or `merge_hi`.  Thus the unchanged galloped
prefix and suffix are part of the observable result. -/
structure MergeAtSelectedPairCorrectness
    (lt : BoolComparator alpha)
    (pre : MergeState (Occurrence alpha) nu) (i : Nat)
    (result : MergeAtResult (Occurrence alpha) nu)
    (left right : PendingRun) : Prop where
  leftSelected : pre.pending[i]? = some left
  rightSelected : pre.pending[i + 1]? = some right
  pendingSplice : ∃ before after,
    before.length = i ∧
      pre.pending.toList = before ++ left :: right :: after ∧
      result.state.pending.toList =
        before ++
          ({ left with len := left.len + right.len } : PendingRun) :: after
  combinedLength :
    (left.len + right.len).toNat = left.len.toNat + right.len.toNat
  exactRange :
    (sortSliceRangeEntries result.state.data left.base
      (left.len.toNat + right.len.toNat)).toList =
        mergeAtTargetEntries lt pre left right
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.state.data left.base
      (left.len.toNat + right.len.toNat))
  stable : StableOccurrencePermutation lt
    ((mergeAtLeftEntries pre left).map SortSliceEntry.key ++
      (mergeAtRightEntries pre right).map SortSliceEntry.key)
    (sortSliceRangeKeys result.state.data left.base
      (left.len.toNat + right.len.toNat)).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.state.data left.base
      (left.len.toNat + right.len.toNat)).toList.Perm
        ((mergeAtLeftEntries pre left) ++ (mergeAtRightEntries pre right))
  frame : SortSlice.EqualOutsideRange pre.data result.state.data left.base
    (left.len.toNat + right.len.toNat)

/-- End-to-end correctness at the public scan/collapse boundary. -/
structure MergeAtCorrectnessPost
    (lt : BoolComparator alpha) (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) : Prop where
  safety : MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) result
  selected : ∃ left right,
    MergeAtSelectedPairCorrectness lt pre i result left right
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

/-- Exact whole-entry output closes to all public selected-pair properties. -/
theorem mergeAtSelectedPairCorrectness_of_exactRange
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {pre : MergeState (Occurrence alpha) nu} {i : Nat}
    {result : MergeAtResult (Occurrence alpha) nu}
    {left right : PendingRun}
    (hleftSelected : pre.pending[i]? = some left)
    (hrightSelected : pre.pending[i + 1]? = some right)
    (hpendingSplice : ∃ before after,
      before.length = i ∧
        pre.pending.toList = before ++ left :: right :: after ∧
        result.state.pending.toList =
          before ++
            ({ left with len := left.len + right.len } : PendingRun) :: after)
    (hcombinedLength :
      (left.len + right.len).toNat = left.len.toNat + right.len.toNat)
    (hleftSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys pre.data left.base left.len.toNat))
    (hrightSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys pre.data right.base right.len.toNat))
    (hstableInput : StableOccurrencePermutation lt
      ((mergeAtLeftEntries pre left).map SortSliceEntry.key ++
        (mergeAtRightEntries pre right).map SortSliceEntry.key)
      ((mergeAtLeftEntries pre left).map SortSliceEntry.key ++
        (mergeAtRightEntries pre right).map SortSliceEntry.key))
    (hexact :
      (sortSliceRangeEntries result.state.data left.base
        (left.len.toNat + right.len.toNat)).toList =
          mergeAtTargetEntries lt pre left right)
    (hframe : SortSlice.EqualOutsideRange pre.data result.state.data left.base
      (left.len.toNat + right.len.toNat)) :
    MergeAtSelectedPairCorrectness lt pre i result left right := by
  have hleftPairwise :
      ((mergeAtLeftEntries pre left).map SortSliceEntry.key).Pairwise
        (DescendingRunSpec.SortedRelation lt) := by
    unfold DescendingRunSpec.SortedRelation
    simpa [Sorted, mergeAtLeftEntries, sortSliceRangeKeys] using hleftSorted
  have hrightPairwise :
      ((mergeAtRightEntries pre right).map SortSliceEntry.key).Pairwise
        (DescendingRunSpec.SortedRelation lt) := by
    unfold DescendingRunSpec.SortedRelation
    simpa [Sorted, mergeAtRightEntries, sortSliceRangeKeys] using hrightSorted
  have hpure := stableEntryMerge_correct horder
    ((mergeAtLeftEntries pre left).map SortSliceEntry.key ++
      (mergeAtRightEntries pre right).map SortSliceEntry.key)
    (mergeAtLeftEntries pre left) (mergeAtRightEntries pre right)
    hleftPairwise hrightPairwise
    hstableInput
  have hkeys :
      (sortSliceRangeKeys result.state.data left.base
        (left.len.toNat + right.len.toNat)).toList =
        (mergeAtTargetEntries lt pre left right).map SortSliceEntry.key := by
    simpa [sortSliceRangeKeys] using
      congrArg (List.map SortSliceEntry.key) hexact
  refine
    { leftSelected := hleftSelected
      rightSelected := hrightSelected
      pendingSplice := hpendingSplice
      combinedLength := hcombinedLength
      exactRange := hexact
      sorted := ?_
      stable := ?_
      rangeEntriesPerm := ?_
      frame := hframe }
  · unfold Sorted
    rw [hkeys]
    exact hpure.1
  · rw [hkeys]
    exact hpure.2.1
  · rw [hexact]
    exact hpure.2.2

/-! ## Trimming facts -/

/-- A bounded main-data range is exactly the key array presented to the
gallop-correctness interface. -/
private theorem gallopKeyArrayAgreement_main_range
    (slice : SortSlice alpha nu) (base n : Nat)
    (hstop : base + n ≤ slice.entries.size) :
    GallopKeyArrayAgreement
      (GallopKeySource.main slice (Int.ofNat base)) n
      (sortSliceRangeKeys slice base n) := by
  refine ⟨sortSliceRangeKeys_size slice base n hstop, ?_⟩
  intro i hi
  let entry := slice.entries[base + i]'(by omega)
  refine ⟨entry, ?_, ?_⟩
  · change slice.read? (Int.ofNat base + Int.ofNat i) = some entry
    rw [show Int.ofNat base + Int.ofNat i = Int.ofNat (base + i) by norm_num,
      SortSlice.read?_ofNat]
    exact Array.getElem?_eq_getElem (by omega)
  · rw [Array.getElem?_eq_getElem (by
      rw [sortSliceRangeKeys_size slice base n hstop]
      exact hi)]
    congr 1
    exact sortSliceRangeKeys_getElem slice base n i hstop hi

/-- Sortedness is inherited by every contained half-open subrange. -/
private theorem sorted_subrange
    (lt : BoolComparator alpha) (slice : SortSlice alpha nu)
    (start total offset count : Nat)
    (hsorted : Sorted lt (sortSliceRangeKeys slice start total))
    (hinside : offset + count ≤ total) :
    Sorted lt (sortSliceRangeKeys slice (start + offset) count) := by
  unfold Sorted at hsorted ⊢
  have hrepr :
      (sortSliceRangeKeys slice (start + offset) count).toList =
        ((sortSliceRangeKeys slice start total).toList.drop offset).take count := by
    rw [sortSliceRangeKeys_toList, sortSliceRangeKeys_toList]
    simp only [List.map_drop, List.map_take, List.drop_take, List.drop_drop]
    rw [show start + offset = offset + start by omega]
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [hrepr]
  exact hsorted.drop.take

/-- A successful read at the first cell identifies the head of a nonempty
bounded whole-entry range. -/
private theorem rangeEntries_eq_cons_of_first_read
    (slice : SortSlice alpha nu) (start count : Nat)
    (entry : SortSliceEntry alpha nu)
    (hstop : start + count ≤ slice.entries.size) (hcount : 0 < count)
    (hread : slice.read? (Int.ofNat start) = some entry) :
    ∃ tail, (sortSliceRangeEntries slice start count).toList = entry :: tail := by
  have hzero :
      (sortSliceRangeEntries slice start count).toList[0]? = some entry := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by
      rw [sortSliceRangeEntries_size slice start count hstop]
      exact hcount)]
    rw [sortSliceRangeEntries_getElem slice start count 0 hstop hcount]
    rw [SortSlice.read?_ofNat] at hread
    have hentryEq := Option.some.inj
      ((Array.getElem?_eq_getElem (by omega)).symm.trans hread)
    simpa using hentryEq
  have hhead :
      (sortSliceRangeEntries slice start count).toList.head? = some entry := by
    simpa [List.head?_eq_getElem?] using hzero
  exact List.head?_eq_some_iff.mp hhead

/-- Pointwise list/read bridge for a bounded whole-entry range. -/
private theorem rangeEntries_getElem?_eq_read
    (slice : SortSlice alpha nu) (start count i : Nat)
    (hstop : start + count ≤ slice.entries.size) (hi : i < count) :
    (sortSliceRangeEntries slice start count).toList[i]? =
      slice.read? (Int.ofNat (start + i)) := by
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by
    rw [sortSliceRangeEntries_size slice start count hstop]
    exact hi)]
  rw [sortSliceRangeEntries_getElem slice start count i hstop hi,
    SortSlice.read?_ofNat, Array.getElem?_eq_getElem (by omega)]

/-- A successful read at the final cell identifies `getLast` of a nonempty
bounded whole-entry range. -/
private theorem rangeEntries_getLast_eq_of_last_read
    (slice : SortSlice alpha nu) (start count : Nat)
    (entry : SortSliceEntry alpha nu)
    (hstop : start + count ≤ slice.entries.size) (hcount : 0 < count)
    (hread : slice.read? (Int.ofNat (start + count - 1)) = some entry) :
    (sortSliceRangeEntries slice start count).toList.getLast (by
      change (sortSliceRangeEntries slice start count).toList ≠ []
      intro hempty
      have hlength := congrArg List.length hempty
      simp [sortSliceRangeEntries_size slice start count hstop] at hlength
      omega) = entry := by
  let entries := (sortSliceRangeEntries slice start count).toList
  have hne : entries ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [entries, Array.length_toList,
      sortSliceRangeEntries_size slice start count hstop,
      List.length_nil] at hlength
    omega
  have hlength :
      entries.length = count := by
    change (sortSliceRangeEntries slice start count).size = count
    exact sortSliceRangeEntries_size slice start count hstop
  have hindex : count - 1 < count := by omega
  have hget : entries[count - 1]? = some entry := by
    change (sortSliceRangeEntries slice start count).toList[count - 1]? =
      some entry
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by
      rw [sortSliceRangeEntries_size slice start count hstop]
      exact hindex)]
    rw [sortSliceRangeEntries_getElem slice start count (count - 1)
      hstop hindex]
    rw [SortSlice.read?_ofNat] at hread
    have harith : start + (count - 1) = start + count - 1 := by omega
    have hsource : slice.entries[start + (count - 1)]? = some entry := by
      simpa only [harith] using hread
    exact (Array.getElem?_eq_getElem (by omega)).symm.trans hsource
  apply Option.some.inj
  calc
    some (entries.getLast hne) = entries.getLast? :=
      (List.getLast?_eq_some_getLast hne).symm
    _ = entries[entries.length - 1]? := List.getLast?_eq_getElem?
    _ = entries[count - 1]? := by rw [hlength]
    _ = some entry := hget

/-- Runs before and after a selected adjacent pair are geometrically disjoint
from the pair's complete union. -/
private theorem PendingRunsCover.pair_member_separation
    {cursor limit : Nat} {before after : List PendingRun}
    {left right : PendingRun}
    (hcover : PendingRunsCover cursor limit
      (before ++ left :: right :: after)) :
    (∀ run ∈ before, run.endIndex ≤ left.base) ∧
      (∀ run ∈ after, right.endIndex ≤ run.base) := by
  induction before generalizing cursor with
  | nil =>
      simp only [List.nil_append, PendingRunsCover] at hcover
      rcases hcover with
        ⟨_hleftBase, _hleftNN, _hleftPos, _hleftEnd,
          hrightBase, _hrightNN, _hrightPos, _hrightEnd, hafter⟩
      refine ⟨by simp, ?_⟩
      intro run hrun
      have hspec := hafter.member_spec hrun
      exact hspec.1
  | cons head before ih =>
      simp only [List.cons_append, PendingRunsCover] at hcover
      rcases hcover with
        ⟨_hheadBase, _hheadNN, _hheadPos, _hheadEnd, htail⟩
      rcases ih htail with ⟨hbefore, hafter⟩
      refine ⟨?_, hafter⟩
      intro run hrun
      simp only [List.mem_cons] at hrun
      rcases hrun with rfl | hrun
      · exact (htail.member_spec (run := left) (by simp)).1
      · exact hbefore run hrun

/-- All semantic facts carried from the two `merge_at` gallops to either
directional merge implementation. -/
private structure MergeAtCallCorrectnessPre
    (lt : BoolComparator alpha)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) : Prop where
  evidence : MergeAtCallsiteEvidence pre i call
  geometry : MergeAtSafetyGeometry pre scanned i call
  pairGeometry : PendingAdjacentPairGeometry pre scanned call.left call.right
  leftStop : call.left.base + call.left.len.toNat ≤ pre.data.entries.size
  rightStop : call.right.base + call.right.len.toNat ≤ pre.data.entries.size
  leftFullSorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys pre.data call.left.base call.left.len.toNat)
  rightFullSorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys pre.data call.right.base call.right.len.toNat)
  fullStable : StableOccurrencePermutation lt
    ((pendingRunOccurrenceKeys pre call.left).toList ++
      (pendingRunOccurrenceKeys pre call.right).toList)
    ((pendingRunOccurrenceKeys pre call.left).toList ++
      (pendingRunOccurrenceKeys pre call.right).toList)
  leftPartition : GallopRightPartition (occurrenceComparator lt)
    call.state.data (Int.ofNat call.left.base) call.firstB.key
    call.left.len.toNat call.trimA.index
  rightPartition : GallopLeftPartition (occurrenceComparator lt)
    call.state.data (Int.ofNat call.right.base) call.lastA.key
    call.right.len.toNat call.trimB.index
  semantic : MergeSemanticPre lt call
  trimmedStable : StableOccurrencePermutation lt
    ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList)
    ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList)

private theorem mergeAtCall_correctnessPre
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {input : Array alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hcorrect : PendingRunsCorrect lt input pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hevidence : MergeAtCallsiteEvidence pre i call)
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (hcallComparator : call.state.key_compare = occurrenceComparator lt) :
    MergeAtCallCorrectnessPre lt pre scanned i call := by
  rcases Array.exists_pair_split_of_getElem?_eq_some
      hevidence.leftSelected hevidence.rightSelected with
    ⟨before, after, _hbeforeLength, hsplit⟩
  have hleftMember : call.left ∈ pre.pending.toList := by
    rw [hsplit]
    simp
  have hrightMember : call.right ∈ pre.pending.toList := by
    rw [hsplit]
    simp
  have hleftFullSorted := hcorrect.runSorted call.left hleftMember
  have hrightFullSorted := hcorrect.runSorted call.right hrightMember
  have hpairGeometry := hcorrect.layout.adjacentPair_geometry
    hevidence.leftSelected hevidence.rightSelected
  have hleftStop :
      call.left.base + call.left.len.toNat ≤ pre.data.entries.size := by
    have hscan : pre.basekeys + scanned ≤
        pre.basekeys + pre.listlen.toNat := by
      exact Nat.add_le_add_left hcorrect.layout.2.2.1 pre.basekeys
    have hleftEnd :
        call.left.base + call.left.len.toNat ≤ pre.basekeys + scanned := by
      rw [show call.left.base + call.left.len.toNat = call.right.base by
        simpa only [PendingRun.endIndex] using hpairGeometry.adjacent]
      have hrightBaseEnd : call.right.base ≤ call.right.endIndex := by
        simp only [PendingRun.endIndex]
        omega
      exact hrightBaseEnd.trans hpairGeometry.rightEnd
    exact hleftEnd.trans (hscan.trans hcorrect.layout.2.1)
  have hrightStop :
      call.right.base + call.right.len.toNat ≤ pre.data.entries.size := by
    have hscan : pre.basekeys + scanned ≤
        pre.basekeys + pre.listlen.toNat := by
      exact Nat.add_le_add_left hcorrect.layout.2.2.1 pre.basekeys
    have hrightEnd :
        call.right.base + call.right.len.toNat ≤ pre.basekeys + scanned := by
      simpa only [PendingRun.endIndex] using hpairGeometry.rightEnd
    exact hrightEnd.trans (hscan.trans hcorrect.layout.2.1)
  have hcallOrder : BoolStrictWeakOrder call.state.key_compare := by
    rw [hcallComparator]
    exact horder.occurrenceComparator
  have hleftCallSorted : Sorted call.state.key_compare
      (sortSliceRangeKeys call.state.data call.left.base
        call.left.len.toNat) := by
    rw [hcallComparator, hevidence.data_eq]
    simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
      hleftFullSorted
  have hrightCallSorted : Sorted call.state.key_compare
      (sortSliceRangeKeys call.state.data call.right.base
        call.right.len.toNat) := by
    rw [hcallComparator, hevidence.data_eq]
    simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
      hrightFullSorted
  have hleftValid :
      (GallopKeySource.main call.state.data
        (Int.ofNat call.left.base)).ValidRange call.left.len.toNat := by
    apply GallopKeySource.main_validRange_of_base_add_le
    rw [hevidence.data_eq]
    exact hleftStop
  have hrightValid :
      (GallopKeySource.main call.state.data
        (Int.ofNat call.right.base)).ValidRange call.right.len.toNat := by
    apply GallopKeySource.main_validRange_of_base_add_le
    rw [hevidence.data_eq]
    exact hrightStop
  have hleftAgreement := gallopKeyArrayAgreement_main_range call.state.data
    call.left.base call.left.len.toNat (by
      rw [hevidence.data_eq]
      exact hleftStop)
  have hrightAgreement := gallopKeyArrayAgreement_main_range call.state.data
    call.right.base call.right.len.toNat (by
      rw [hevidence.data_eq]
      exact hrightStop)
  have hleftLenMax : call.left.len.toNat ≤ PY_LIST_MAX :=
    le_trans (le_trans
      ((Nat.le_add_right call.left.len.toNat call.right.len.toNat).trans
        hpairGeometry.pairSpan)
      hpairGeometry.scannedBound) hmax
  have hrightLenMax : call.right.len.toNat ≤ PY_LIST_MAX :=
    le_trans (le_trans
      ((Nat.le_add_left call.right.len.toNat call.left.len.toNat).trans
        hpairGeometry.pairSpan)
      hpairGeometry.scannedBound) hmax
  rcases gallopRight_correct_of_sorted call.state
      (.main call.state.data (Int.ofNat call.left.base)) call.state.data
      (Int.ofNat call.left.base) call.firstB.key call.left.len.toNat 0
      (sortSliceRangeKeys call.state.data call.left.base call.left.len.toNat)
      hleftValid (by simp) hleftAgreement hcallOrder hleftCallSorted
      hpairGeometry.leftPositive hpairGeometry.leftPositive hleftLenMax with
    ⟨trimA, htrimA, _htrimAFuel, hleftPartitionRaw⟩
  have htrimAEq : trimA = call.trimA := by
    exact Option.some.inj (htrimA.symm.trans hevidence.rightGallop)
  subst trimA
  have hleftPartition : GallopRightPartition (occurrenceComparator lt)
      call.state.data (Int.ofNat call.left.base) call.firstB.key
      call.left.len.toNat call.trimA.index := by
    rw [← hcallComparator]
    exact hleftPartitionRaw
  rcases gallopLeft_correct_of_sorted call.state
      (.main call.state.data (Int.ofNat call.right.base)) call.state.data
      (Int.ofNat call.right.base) call.lastA.key call.right.len.toNat
      (call.right.len.toNat - 1)
      (sortSliceRangeKeys call.state.data call.right.base call.right.len.toNat)
      hrightValid (by simp) hrightAgreement hcallOrder hrightCallSorted
      hpairGeometry.rightPositive
      (Nat.sub_lt hpairGeometry.rightPositive (by omega)) hrightLenMax with
    ⟨trimB, htrimB, _htrimBFuel, hrightPartitionRaw⟩
  have htrimBEq : trimB = call.trimB := by
    exact Option.some.inj (htrimB.symm.trans hevidence.leftGallop)
  subst trimB
  have hrightPartition : GallopLeftPartition (occurrenceComparator lt)
      call.state.data (Int.ofNat call.right.base) call.lastA.key
      call.right.len.toNat call.trimB.index := by
    rw [← hcallComparator]
    exact hrightPartitionRaw
  have hssaNat : call.ssa.toNat = call.left.base + call.trimA.index := by
    rw [hevidence.ssa_eq]
    rfl
  have hssbNat : call.ssb.toNat = call.right.base := by
    rw [hevidence.ssb_eq]
    rfl
  have hleftTrimSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys call.state.data call.ssa.toNat call.na) := by
    rw [hevidence.data_eq, hssaNat, hevidence.leftRemainder]
    apply sorted_subrange (occurrenceComparator lt) pre.data call.left.base
      call.left.len.toNat call.trimA.index
      (call.left.len.toNat - call.trimA.index)
    · simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
        hleftFullSorted
    · exact Nat.add_sub_of_le hleftPartition.1 |>.le
  have hrightTrimSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb) := by
    rw [hevidence.data_eq, hssbNat, hevidence.rightRemainder]
    apply sorted_subrange (occurrenceComparator lt) pre.data call.right.base
      call.right.len.toNat 0 call.trimB.index
    · simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
        hrightFullSorted
    · simpa using hrightPartition.1
  have hfirstStrict : ∃ firstLeft firstRight,
      call.state.data.read? call.ssa = some firstLeft ∧
      call.state.data.read? call.ssb = some firstRight ∧
      lt firstRight.key.value firstLeft.key.value = true := by
    have htrimAlt : call.trimA.index < call.left.len.toNat := by
      have hpositive := hevidence.leftPositive
      rw [hevidence.leftRemainder] at hpositive
      omega
    rcases hleftPartition.2.2 call.trimA.index (by omega) htrimAlt with
      ⟨firstLeft, hfirstLeft, hcompare⟩
    refine ⟨firstLeft, call.firstB, ?_, ?_, ?_⟩
    · rw [hevidence.ssa_eq]
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hfirstLeft
    · rw [hevidence.ssb_eq]
      exact hevidence.firstBRead
    · exact hcompare
  have hlastStrict : ∃ lastLeft lastRight,
      call.state.data.read?
          (call.ssa + Int.ofNat (call.na - 1)) = some lastLeft ∧
      call.state.data.read?
          (call.ssb + Int.ofNat (call.nb - 1)) = some lastRight ∧
      lt lastRight.key.value lastLeft.key.value = true := by
    have hindex : call.nb - 1 < call.trimB.index := by
      have hpositive := hevidence.rightPositive
      rw [hevidence.rightRemainder] at hpositive
      rw [hevidence.rightRemainder]
      omega
    rcases hrightPartition.2.1 (call.nb - 1) hindex with
      ⟨lastRight, hlastRight, hcompare⟩
    refine ⟨call.lastA, lastRight, ?_, ?_, ?_⟩
    · have hlastA := hevidence.lastARead
      have harith :
          call.left.base + call.trimA.index + call.na - 1 =
            call.left.base + call.trimA.index + (call.na - 1) := by
        have hpositive := hevidence.leftPositive
        omega
      rw [harith] at hlastA
      rw [hevidence.ssa_eq]
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hlastA
    · rw [hevidence.ssb_eq]
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hlastRight
    · exact hcompare
  have hsemantic : MergeSemanticPre lt call :=
    { leftNonempty := hevidence.leftPositive
      rightNonempty := hevidence.rightPositive
      leftSorted := hleftTrimSorted
      rightSorted := hrightTrimSorted
      firstStrict := hfirstStrict
      lastStrict := hlastStrict }
  have hglobalDecomposition := pendingOccurrenceKeys_pair_decomposition hsplit
  have hfullSublist :
      ((pendingRunOccurrenceKeys pre call.left).toList ++
        (pendingRunOccurrenceKeys pre call.right).toList).Sublist
          (pendingOccurrenceKeys pre) := by
    rw [hglobalDecomposition]
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using
      (((List.nil_sublist (pendingOccurrenceKeysOf pre before)).append
        ((List.Sublist.refl
          (pendingRunOccurrenceKeys pre call.left).toList).append
          (List.Sublist.refl
            (pendingRunOccurrenceKeys pre call.right).toList))).append
        (List.nil_sublist (pendingOccurrenceKeysOf pre after)))
  have hfullPairwise := hcorrect.pending_stable.sublist hfullSublist
  have hfullStable : StableOccurrencePermutation lt
      ((pendingRunOccurrenceKeys pre call.left).toList ++
        (pendingRunOccurrenceKeys pre call.right).toList)
      ((pendingRunOccurrenceKeys pre call.left).toList ++
        (pendingRunOccurrenceKeys pre call.right).toList) :=
    ⟨List.Perm.refl _, hfullPairwise⟩
  have hleftTrimEq :
      (sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList =
        (pendingRunOccurrenceKeys pre call.left).toList.drop
          call.trimA.index := by
    rw [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
      sortSliceRangeKeys_toList_drop, ← hevidence.leftRemainder,
      ← hssaNat, hevidence.data_eq]
  have hrightTrimEq :
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList =
        (pendingRunOccurrenceKeys pre call.right).toList.take
          call.trimB.index := by
    rw [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
      hevidence.data_eq, hssbNat, hevidence.rightRemainder]
    rw [sortSliceRangeKeys_toList, sortSliceRangeKeys_toList]
    simp only [List.map_take, List.take_take]
    rw [Nat.min_eq_left hrightPartition.1]
  have htrimmedSublist :
      ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
        (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList).Sublist
      ((pendingRunOccurrenceKeys pre call.left).toList ++
        (pendingRunOccurrenceKeys pre call.right).toList) := by
    rw [hleftTrimEq, hrightTrimEq]
    exact (List.drop_sublist _ _).append (List.take_sublist _ _)
  have htrimmedPairwise := hfullPairwise.sublist htrimmedSublist
  exact
    { evidence := hevidence
      geometry := hgeometry
      pairGeometry := hpairGeometry
      leftStop := hleftStop
      rightStop := hrightStop
      leftFullSorted := by
        simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
          hleftFullSorted
      rightFullSorted := by
        simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
          hrightFullSorted
      fullStable := hfullStable
      leftPartition := hleftPartition
      rightPartition := hrightPartition
      semantic := hsemantic
      trimmedStable := ⟨List.Perm.refl _, htrimmedPairwise⟩ }

/-- If the first gallop consumes all of the left run, every left entry already
belongs before the right head and the stable merge is unchanged
concatenation. -/
private theorem stableEntryMerge_eq_append_of_gallopRight_end
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu)
    (leftBase leftCount rightBase rightCount : Nat)
    (firstB : SortSliceEntry (Occurrence alpha) nu)
    (trimA : GallopResult)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hleftStop : leftBase + leftCount ≤ slice.entries.size)
    (hrightStop : rightBase + rightCount ≤ slice.entries.size)
    (hleftSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys slice leftBase leftCount))
    (hleftPositive : 0 < leftCount) (hrightPositive : 0 < rightCount)
    (hleftMax : leftCount ≤ PY_LIST_MAX)
    (hfirstB : slice.read? (Int.ofNat rightBase) = some firstB)
    (htrimA : gallopRight? state slice (Int.ofNat leftBase)
      firstB.key leftCount 0 = some trimA)
    (hend : trimA.index = leftCount) :
    stableEntryMerge lt
      (sortSliceRangeEntries slice leftBase leftCount).toList
      (sortSliceRangeEntries slice rightBase rightCount).toList =
      (sortSliceRangeEntries slice leftBase leftCount).toList ++
        (sortSliceRangeEntries slice rightBase rightCount).toList := by
  have hstateOrder : BoolStrictWeakOrder state.key_compare := by
    rw [hcompare]
    exact horder.occurrenceComparator
  have hleftStateSorted : Sorted state.key_compare
      (sortSliceRangeKeys slice leftBase leftCount) := by
    rw [hcompare]
    exact hleftSorted
  rcases gallopRight_correct_of_sorted state
      (.main slice (Int.ofNat leftBase)) slice (Int.ofNat leftBase)
      firstB.key leftCount 0 (sortSliceRangeKeys slice leftBase leftCount)
      (GallopKeySource.main_validRange_of_base_add_le slice leftBase leftCount
        hleftStop) (by simp)
      (gallopKeyArrayAgreement_main_range slice leftBase leftCount hleftStop)
      hstateOrder hleftStateSorted hleftPositive hleftPositive hleftMax with
    ⟨actualA, hactualA, _hfuelA, hpartitionRaw⟩
  have hactualAEq : actualA = trimA :=
    Option.some.inj (hactualA.symm.trans htrimA)
  subst actualA
  have hpartition : GallopRightPartition (occurrenceComparator lt) slice
      (Int.ofNat leftBase) firstB.key leftCount trimA.index := by
    rw [← hcompare]
    exact hpartitionRaw
  rcases rangeEntries_eq_cons_of_first_read slice rightBase rightCount firstB
      hrightStop hrightPositive hfirstB with ⟨rightTail, hright⟩
  have hblock : ∀ entry ∈
      (sortSliceRangeEntries slice leftBase leftCount).toList,
      lt firstB.key.value entry.key.value = false := by
    intro entry hentry
    rcases List.mem_iff_getElem?.mp hentry with ⟨j, hj⟩
    have hjlt : j < leftCount := by
      rcases List.getElem?_eq_some_iff.mp hj with ⟨hjlt, _⟩
      simpa only [Array.length_toList,
        sortSliceRangeEntries_size slice leftBase leftCount hleftStop] using
        hjlt
    rcases hpartition.2.1 j (by omega) with
      ⟨found, hfound, hcomparison⟩
    have hentryRead : slice.read? (Int.ofNat (leftBase + j)) = some entry := by
      rw [← rangeEntries_getElem?_eq_read slice leftBase leftCount j
        hleftStop hjlt]
      exact hj
    have hfoundRead : slice.read? (Int.ofNat (leftBase + j)) = some found := by
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hfound
    have hfoundEq : found = entry :=
      Option.some.inj (hfoundRead.symm.trans hentryRead)
    subst found
    exact hcomparison
  rw [hright]
  simpa [stableEntryMerge] using stableEntryMerge_left_prefix lt
    (sortSliceRangeEntries slice leftBase leftCount).toList [] firstB
    rightTail hblock

/-- Under a strict weak order and sorted adjacent runs, the defensive
post-second-gallop `nb = 0` success branch is unreachable once the first
gallop retained a nonempty left suffix.  This theorem is public so reviewers
and downstream correctness proofs can cite the exact branch exclusion. -/
theorem mergeAt_secondTrimZero_impossible
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu)
    (leftBase leftCount rightBase rightCount : Nat)
    (firstB lastA : SortSliceEntry (Occurrence alpha) nu)
    (trimA trimB : GallopResult)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hleftStop : leftBase + leftCount ≤ slice.entries.size)
    (hrightStop : rightBase + rightCount ≤ slice.entries.size)
    (hleftSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys slice leftBase leftCount))
    (hrightSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys slice rightBase rightCount))
    (hleftPositive : 0 < leftCount) (hrightPositive : 0 < rightCount)
    (hleftMax : leftCount ≤ PY_LIST_MAX)
    (hrightMax : rightCount ≤ PY_LIST_MAX)
    (hfirstB : slice.read? (Int.ofNat rightBase) = some firstB)
    (htrimA : gallopRight? state slice (Int.ofNat leftBase)
      firstB.key leftCount 0 = some trimA)
    (hnaPositive : 0 < leftCount - trimA.index)
    (hlastA : slice.read?
      (Int.ofNat (leftBase + trimA.index +
        (leftCount - trimA.index) - 1)) = some lastA)
    (htrimB : gallopLeft? state slice (Int.ofNat rightBase)
      lastA.key rightCount (rightCount - 1) = some trimB)
    (hzero : trimB.index = 0) : False := by
  have hstateOrder : BoolStrictWeakOrder state.key_compare := by
    rw [hcompare]
    exact horder.occurrenceComparator
  have hleftStateSorted : Sorted state.key_compare
      (sortSliceRangeKeys slice leftBase leftCount) := by
    rw [hcompare]
    exact hleftSorted
  rcases gallopRight_correct_of_sorted state
      (.main slice (Int.ofNat leftBase)) slice (Int.ofNat leftBase)
      firstB.key leftCount 0 (sortSliceRangeKeys slice leftBase leftCount)
      (GallopKeySource.main_validRange_of_base_add_le slice leftBase leftCount
        hleftStop) (by simp)
      (gallopKeyArrayAgreement_main_range slice leftBase leftCount hleftStop)
      hstateOrder hleftStateSorted hleftPositive hleftPositive hleftMax with
    ⟨actualA, hactualA, _hfuelA, hpartitionARaw⟩
  have hactualAEq : actualA = trimA :=
    Option.some.inj (hactualA.symm.trans htrimA)
  subst actualA
  have hpartitionA : GallopRightPartition (occurrenceComparator lt) slice
      (Int.ofNat leftBase) firstB.key leftCount trimA.index := by
    rw [← hcompare]
    exact hpartitionARaw
  have htrimAlt : trimA.index < leftCount := by omega
  rcases hpartitionA.2.2 trimA.index (by omega) htrimAlt with
    ⟨firstA, hfirstA, hfirstStrict⟩
  have hlastIndex :
      leftBase + trimA.index + (leftCount - trimA.index) - 1 =
        leftBase + (leftCount - 1) := by omega
  have hlastA' : slice.read? (Int.ofNat (leftBase + (leftCount - 1))) =
      some lastA := by
    rw [← hlastIndex]
    exact hlastA
  have hfirstARead : slice.read? (Int.ofNat (leftBase + trimA.index)) =
      some firstA := by
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hfirstA
  have hlastNotBefore : lt lastA.key.value firstA.key.value = false := by
    by_cases hindices : trimA.index < leftCount - 1
    · have hsortedIndex := (sorted_iff_no_later_precedes
          (occurrenceComparator lt)
          (sortSliceRangeKeys slice leftBase leftCount)).1 hleftSorted
          trimA.index (leftCount - 1)
          (by
            rw [sortSliceRangeKeys_size slice leftBase leftCount hleftStop]
            exact htrimAlt)
          (by
            rw [sortSliceRangeKeys_size slice leftBase leftCount hleftStop]
            omega)
          hindices
      have hfirstKey :
          (sortSliceRangeKeys slice leftBase leftCount)[trimA.index]'(by
            rw [sortSliceRangeKeys_size slice leftBase leftCount hleftStop]
            exact htrimAlt) = firstA.key := by
        rw [sortSliceRangeKeys_getElem slice leftBase leftCount trimA.index
          hleftStop htrimAlt]
        rw [SortSlice.read?_ofNat] at hfirstARead
        exact congrArg SortSliceEntry.key (Option.some.inj
          ((Array.getElem?_eq_getElem (by omega)).symm.trans hfirstARead))
      have hlastKey :
          (sortSliceRangeKeys slice leftBase leftCount)[leftCount - 1]'(by
            rw [sortSliceRangeKeys_size slice leftBase leftCount hleftStop]
            omega) = lastA.key := by
        rw [sortSliceRangeKeys_getElem slice leftBase leftCount
          (leftCount - 1) hleftStop (by omega)]
        rw [SortSlice.read?_ofNat] at hlastA'
        exact congrArg SortSliceEntry.key (Option.some.inj
          ((Array.getElem?_eq_getElem (by omega)).symm.trans hlastA'))
      apply Bool.eq_false_of_not_eq_true
      intro hstrict
      apply hsortedIndex
      change occurrenceComparator lt
        ((sortSliceRangeKeys slice leftBase leftCount)[leftCount - 1]'(by
          rw [sortSliceRangeKeys_size slice leftBase leftCount hleftStop]
          omega))
        ((sortSliceRangeKeys slice leftBase leftCount)[trimA.index]'(by
          rw [sortSliceRangeKeys_size slice leftBase leftCount hleftStop]
          exact htrimAlt)) = true
      rw [hfirstKey, hlastKey]
      exact hstrict
    · have hindexEq : trimA.index = leftCount - 1 := by omega
      have hentryEq : firstA = lastA := by
        apply Option.some.inj
        calc
          some firstA = slice.read?
              (Int.ofNat (leftBase + trimA.index)) := hfirstARead.symm
          _ = slice.read? (Int.ofNat (leftBase + (leftCount - 1))) := by
            rw [hindexEq]
          _ = some lastA := hlastA'
      subst lastA
      exact Bool.eq_false_iff.mpr (horder.irrefl firstA.key.value)
  have hfirstLast : lt firstB.key.value lastA.key.value = true :=
    horder.strict_of_strict_of_not_reverse hfirstStrict hlastNotBefore
  have hrightStateSorted : Sorted state.key_compare
      (sortSliceRangeKeys slice rightBase rightCount) := by
    rw [hcompare]
    exact hrightSorted
  rcases gallopLeft_correct_of_sorted state
      (.main slice (Int.ofNat rightBase)) slice (Int.ofNat rightBase)
      lastA.key rightCount (rightCount - 1)
      (sortSliceRangeKeys slice rightBase rightCount)
      (GallopKeySource.main_validRange_of_base_add_le slice rightBase
        rightCount hrightStop) (by simp)
      (gallopKeyArrayAgreement_main_range slice rightBase rightCount hrightStop)
      hstateOrder hrightStateSorted hrightPositive
      (Nat.sub_lt hrightPositive (by omega)) hrightMax with
    ⟨actualB, hactualB, _hfuelB, hpartitionBRaw⟩
  have hactualBEq : actualB = trimB :=
    Option.some.inj (hactualB.symm.trans htrimB)
  subst actualB
  have hpartitionB : GallopLeftPartition (occurrenceComparator lt) slice
      (Int.ofNat rightBase) lastA.key rightCount trimB.index := by
    rw [← hcompare]
    exact hpartitionBRaw
  rcases hpartitionB.2.2 0 (by omega) hrightPositive with
    ⟨rightHead, hrightHead, hnotStrict⟩
  have hrightHeadRead : slice.read? (Int.ofNat rightBase) =
      some rightHead := by
    simpa using hrightHead
  have hrightHeadEq : rightHead = firstB :=
    Option.some.inj (hrightHeadRead.symm.trans hfirstB)
  subst rightHead
  exact Bool.noConfusion (hnotStrict.symm.trans hfirstLast)

/-- Lift a correct merge of the post-gallop middle to the complete selected
pair, reattaching the galloped prefix and suffix in their final positions. -/
private theorem mergeAtCall_lift_full_pair
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtCallCorrectnessPre lt pre scanned i call)
    {after : SortSlice (Occurrence alpha) nu}
    (hlocalExact :
      (sortSliceRangeEntries after call.ssa.toNat
        (call.na + call.nb)).toList =
        stableEntryMerge lt
          (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList
          (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList)
    (hlocalFrame : SortSlice.EqualOutsideRange call.state.data after
      call.ssa.toNat (call.na + call.nb)) :
    (sortSliceRangeEntries after call.left.base
        (call.left.len.toNat + call.right.len.toNat)).toList =
          mergeAtTargetEntries lt pre call.left call.right ∧
      SortSlice.EqualOutsideRange pre.data after call.left.base
        (call.left.len.toNat + call.right.len.toNat) := by
  have hssaNat : call.ssa.toNat =
      call.left.base + call.trimA.index := by
    rw [h.evidence.ssa_eq]
    rfl
  have hssbNat : call.ssb.toNat = call.right.base := by
    rw [h.evidence.ssb_eq]
    rfl
  have hleftTotal :
      call.trimA.index + call.na = call.left.len.toNat := by
    have htrim := h.leftPartition.1
    rw [h.evidence.leftRemainder]
    omega
  have hrightTotal :
      call.nb + (call.right.len.toNat - call.nb) =
        call.right.len.toNat := by
    have htrim := h.rightPartition.1
    rw [h.evidence.rightRemainder]
    omega
  have hadjacent :
      call.left.base + call.left.len.toNat = call.right.base := by
    simpa only [PendingRun.endIndex] using h.pairGeometry.adjacent
  have hmiddleEnd :
      call.ssa.toNat + (call.na + call.nb) =
        call.right.base + call.nb := by
    have hadj := mergeLo_ssa_add_na_toNat h.geometry
    omega
  have hframePre : SortSlice.EqualOutsideRange pre.data after
      call.ssa.toNat (call.na + call.nb) := by
    rw [← h.evidence.data_eq]
    exact hlocalFrame
  have hfullFrame : SortSlice.EqualOutsideRange pre.data after
      call.left.base (call.left.len.toNat + call.right.len.toNat) := by
    apply hframePre.widen
    · rw [hssaNat]
      omega
    · rw [hssaNat]
      omega
  have hprefixEq :
      (sortSliceRangeEntries after call.left.base call.trimA.index).toList =
        (sortSliceRangeEntries pre.data call.left.base
          call.trimA.index).toList := by
    have heq := hframePre.entries_eq_of_disjoint call.left.base
      call.trimA.index (Or.inl (by omega))
    exact congrArg Array.toList heq.symm
  have hsuffixEq :
      (sortSliceRangeEntries after (call.right.base + call.nb)
        (call.right.len.toNat - call.nb)).toList =
      (sortSliceRangeEntries pre.data (call.right.base + call.nb)
        (call.right.len.toNat - call.nb)).toList := by
    have heq := hframePre.entries_eq_of_disjoint
      (call.right.base + call.nb) (call.right.len.toNat - call.nb)
      (Or.inr (by omega))
    exact congrArg Array.toList heq.symm
  have hleftDecomp : mergeAtLeftEntries pre call.left =
      (sortSliceRangeEntries pre.data call.left.base
        call.trimA.index).toList ++
      (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList := by
    unfold mergeAtLeftEntries
    rw [← hleftTotal, sortSliceRangeEntries_toList_add]
    rw [hssaNat, h.evidence.data_eq]
  have hrightDecomp : mergeAtRightEntries pre call.right =
      (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList ++
      (sortSliceRangeEntries pre.data (call.right.base + call.nb)
        (call.right.len.toNat - call.nb)).toList := by
    unfold mergeAtRightEntries
    rw [hssbNat, h.evidence.data_eq]
    simpa only [hrightTotal] using
      (sortSliceRangeEntries_toList_add pre.data call.right.base call.nb
        (call.right.len.toNat - call.nb))
  have hfirstBReadPre :
      pre.data.read? (Int.ofNat call.right.base) = some call.firstB := by
    rw [← h.evidence.data_eq]
    exact h.evidence.firstBRead
  rcases rangeEntries_eq_cons_of_first_read pre.data call.right.base
      call.right.len.toNat call.firstB h.rightStop
      h.pairGeometry.rightPositive hfirstBReadPre with
    ⟨rightTail, hrightHead⟩
  have hrightHead' :
      mergeAtRightEntries pre call.right = call.firstB :: rightTail := by
    exact hrightHead
  have hprefixBefore : ∀ entry ∈
      (sortSliceRangeEntries pre.data call.left.base
        call.trimA.index).toList,
      lt call.firstB.key.value entry.key.value = false := by
    have hprefixStop :
        call.left.base + call.trimA.index ≤ pre.data.entries.size := by
      have htrim := h.leftPartition.1
      exact (Nat.add_le_add_left htrim call.left.base).trans h.leftStop
    intro entry hentry
    rcases List.mem_iff_getElem?.mp hentry with ⟨j, hj⟩
    have hjlt : j < call.trimA.index := by
      rcases List.getElem?_eq_some_iff.mp hj with ⟨hjlt, _⟩
      simpa only [Array.length_toList,
        sortSliceRangeEntries_size pre.data call.left.base
          call.trimA.index hprefixStop] using hjlt
    rcases h.leftPartition.2.1 j hjlt with
      ⟨found, hfound, hcompare⟩
    have hentryRead :
        pre.data.read? (Int.ofNat (call.left.base + j)) = some entry := by
      rw [← rangeEntries_getElem?_eq_read pre.data call.left.base
        call.trimA.index j hprefixStop hjlt]
      exact hj
    have hfoundRead :
        pre.data.read? (Int.ofNat (call.left.base + j)) = some found := by
      rw [← h.evidence.data_eq]
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add, add_assoc] using hfound
    have hfoundEq : found = entry :=
      Option.some.inj (hfoundRead.symm.trans hentryRead)
    subst found
    exact hcompare
  have hleftPeeled := stableEntryMerge_left_prefix lt
    (sortSliceRangeEntries pre.data call.left.base call.trimA.index).toList
    (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList
    call.firstB rightTail hprefixBefore
  have hleftRangeStop :
      call.ssa.toNat + call.na ≤ call.state.data.entries.size := by
    have hmerged := h.geometry.naturalMergedRange
    omega
  have hleftEntriesNe :
      (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [Array.length_toList,
      sortSliceRangeEntries_size call.state.data call.ssa.toNat call.na
        hleftRangeStop,
      List.length_nil] at hlength
    have hpositive := h.semantic.leftNonempty
    omega
  have hleftEntriesPairwise :
      (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList.Pairwise
        (fun earlier later =>
          lt later.key.value earlier.key.value = false) := by
    apply (List.pairwise_map (f := SortSliceEntry.key)
      (R := fun earlier later : Occurrence alpha =>
        lt later.value earlier.value = false)).mp
    simpa [Sorted, sortSliceRangeKeys, occurrenceComparator] using
      h.semantic.leftSorted
  have hlastAReadNat :
      call.state.data.read?
        (Int.ofNat (call.ssa.toNat + call.na - 1)) = some call.lastA := by
    have hread := h.evidence.lastARead
    rw [hssaNat]
    simpa only [hssaNat] using hread
  have hlastA :
      (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList.getLast
        hleftEntriesNe = call.lastA :=
    rangeEntries_getLast_eq_of_last_read call.state.data call.ssa.toNat
      call.na call.lastA hleftRangeStop h.semantic.leftNonempty hlastAReadNat
  have hsuffixBoundary : ∀ suffixEntry ∈
      (sortSliceRangeEntries pre.data (call.right.base + call.nb)
        (call.right.len.toNat - call.nb)).toList,
      lt suffixEntry.key.value call.lastA.key.value = false := by
    have hsuffixStop :
        call.right.base + call.nb + (call.right.len.toNat - call.nb) ≤
          pre.data.entries.size := by
      have hnb : call.nb ≤ call.right.len.toNat := by
        rw [h.evidence.rightRemainder]
        exact h.rightPartition.1
      calc
        call.right.base + call.nb +
            (call.right.len.toNat - call.nb) =
          call.right.base + call.right.len.toNat := by omega
        _ ≤ pre.data.entries.size := h.rightStop
    intro suffixEntry hsuffix
    rcases List.mem_iff_getElem?.mp hsuffix with ⟨j, hj⟩
    have hjlt : j < call.right.len.toNat - call.nb := by
      rcases List.getElem?_eq_some_iff.mp hj with ⟨hjlt, _⟩
      simpa only [Array.length_toList, sortSliceRangeEntries_size pre.data
        (call.right.base + call.nb) (call.right.len.toNat - call.nb)
        hsuffixStop] using hjlt
    have hlogical : call.nb + j < call.right.len.toNat := by omega
    rcases h.rightPartition.2.2 (call.nb + j)
        (by
          rw [h.evidence.rightRemainder]
          exact Nat.le_add_right _ _) hlogical with
      ⟨found, hfound, hcompare⟩
    have hsuffixRead : pre.data.read?
        (Int.ofNat (call.right.base + call.nb + j)) = some suffixEntry := by
      rw [← rangeEntries_getElem?_eq_read pre.data
        (call.right.base + call.nb) (call.right.len.toNat - call.nb) j
        hsuffixStop hjlt]
      exact hj
    have hfoundRead : pre.data.read?
        (Int.ofNat (call.right.base + call.nb + j)) = some found := by
      rw [← h.evidence.data_eq]
      have hbase :
          Int.ofNat call.right.base + Int.ofNat (call.nb + j) =
            Int.ofNat (call.right.base + call.nb + j) := by
        norm_num [Int.ofNat_eq_natCast, Nat.cast_add, add_assoc]
      rw [← hbase]
      exact hfound
    have hfoundEq : found = suffixEntry :=
      Option.some.inj (hfoundRead.symm.trans hsuffixRead)
    subst found
    exact hcompare
  have hsuffixAfter := all_suffix_not_lt_left_of_pairwise_of_not_lt_last
    horder
    (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList
    (sortSliceRangeEntries pre.data (call.right.base + call.nb)
      (call.right.len.toNat - call.nb)).toList
    hleftEntriesNe hleftEntriesPairwise (by
      simpa only [hlastA] using hsuffixBoundary)
  have hrightAppended := stableEntryMerge_append_right_block lt
    (sortSliceRangeEntries pre.data (call.right.base + call.nb)
      (call.right.len.toNat - call.nb)).toList
    (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList
    (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList
    hsuffixAfter
  have htarget : mergeAtTargetEntries lt pre call.left call.right =
      (sortSliceRangeEntries pre.data call.left.base
        call.trimA.index).toList ++
      stableEntryMerge lt
        (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList
        (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList ++
      (sortSliceRangeEntries pre.data (call.right.base + call.nb)
        (call.right.len.toNat - call.nb)).toList := by
    unfold mergeAtTargetEntries
    rw [hleftDecomp, hrightHead', hleftPeeled, hrightHead'.symm,
      hrightDecomp, hrightAppended]
    simp only [List.append_assoc]
  have hafter :
      (sortSliceRangeEntries after call.left.base
        (call.left.len.toNat + call.right.len.toNat)).toList =
      (sortSliceRangeEntries pre.data call.left.base
        call.trimA.index).toList ++
      stableEntryMerge lt
        (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList
        (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList ++
      (sortSliceRangeEntries pre.data (call.right.base + call.nb)
        (call.right.len.toNat - call.nb)).toList := by
    rw [show call.left.len.toNat + call.right.len.toNat =
      call.trimA.index +
        ((call.na + call.nb) + (call.right.len.toNat - call.nb)) by omega]
    rw [sortSliceRangeEntries_toList_add,
      sortSliceRangeEntries_toList_add]
    rw [hprefixEq]
    rw [show call.left.base + call.trimA.index = call.ssa.toNat by omega]
    rw [hlocalExact]
    rw [show call.ssa.toNat + (call.na + call.nb) =
      call.right.base + call.nb by exact hmiddleEnd]
    rw [hsuffixEq]
    simp only [List.append_assoc]
  exact ⟨hafter.trans htarget.symm, hfullFrame⟩

/-- Close one selected-pair certificate to the global pending, snapshot, and
consumed-prefix invariants expected by scan and collapse consumers. -/
private theorem mergeAtCorrectnessPost_of_selected
    {lt : BoolComparator alpha} {input : Array alpha}
    {source : SortSlice alpha nu}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {result : MergeAtResult (Occurrence alpha) nu}
    (hcorrect : PendingRunsCorrect lt input pre scanned)
    (hsnapshot : EntrySnapshotPermutation source pre.data)
    (hcompare : pre.key_compare = occurrenceComparator lt)
    (hsafety : MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) result)
    {left right : PendingRun}
    (hselected : MergeAtSelectedPairCorrectness lt pre i result left right) :
    MergeAtCorrectnessPost lt input source pre scanned i result := by
  rcases hselected.pendingSplice with
    ⟨before, after, hbeforeLength, hbeforePending, hafterPending⟩
  let merged : PendingRun :=
    { left with len := left.len + right.len }
  have hpairGeometry := hcorrect.layout.adjacentPair_geometry
    hselected.leftSelected hselected.rightSelected
  have hcover : PendingRunsCover pre.basekeys (pre.basekeys + scanned)
      (before ++ left :: right :: after) := by
    rw [← hbeforePending]
    exact hcorrect.layout.2.2.2
  rcases hcover.pair_member_separation with
    ⟨hbeforeDisjoint, hafterDisjoint⟩
  have hpairStop :
      left.base + (left.len.toNat + right.len.toNat) ≤
        pre.data.entries.size := by
    have hend : left.base + (left.len.toNat + right.len.toNat) =
        right.endIndex := by
      have hadj : left.base + left.len.toNat = right.base := by
        simpa only [PendingRun.endIndex] using hpairGeometry.adjacent
      simp only [PendingRun.endIndex]
      omega
    rw [hend]
    exact hpairGeometry.rightEnd.trans
      ((Nat.add_le_add_left hcorrect.layout.2.2.1 pre.basekeys).trans
        hcorrect.layout.2.1)
  have hbeforeKeys : ∀ run ∈ before,
      pendingRunOccurrenceKeys pre run =
        pendingRunOccurrenceKeys result.state run := by
    intro run hrun
    apply pendingRunOccurrenceKeys_eq_of_equalOutsideRange run hselected.frame
    exact Or.inl (hbeforeDisjoint run hrun)
  have hafterKeys : ∀ run ∈ after,
      pendingRunOccurrenceKeys pre run =
        pendingRunOccurrenceKeys result.state run := by
    intro run hrun
    apply pendingRunOccurrenceKeys_eq_of_equalOutsideRange run hselected.frame
    right
    have hstart : left.base + (left.len.toNat + right.len.toNat) =
        right.endIndex := by
      have hadj : left.base + left.len.toNat = right.base := by
        simpa only [PendingRun.endIndex] using hpairGeometry.adjacent
      simp only [PendingRun.endIndex]
      omega
    rw [hstart]
    exact hafterDisjoint run hrun
  have hmergedSorted : Sorted (occurrenceComparator lt)
      (pendingRunOccurrenceKeys result.state merged) := by
    simpa [merged, pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
      hselected.combinedLength] using hselected.sorted
  have hmergedStable : StableOccurrencePermutation lt
      ((pendingRunOccurrenceKeys pre left).toList ++
        (pendingRunOccurrenceKeys pre right).toList)
      (pendingRunOccurrenceKeys result.state merged).toList := by
    simpa [merged, pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
      mergeAtLeftEntries, mergeAtRightEntries, sortSliceRangeKeys,
      hselected.combinedLength] using hselected.stable
  have hpendingCorrect := hcorrect.replaceAdjacent hsafety.pendingLayout
    hsafety.stableFrame.basekeys hbeforePending (by
      simpa [merged] using hafterPending) hbeforeKeys hafterKeys
    hmergedSorted hmergedStable
  have hprePairEntries :
      (sortSliceRangeEntries pre.data left.base
        (left.len.toNat + right.len.toNat)).toList =
      mergeAtLeftEntries pre left ++ mergeAtRightEntries pre right := by
    rw [sortSliceRangeEntries_toList_add]
    unfold mergeAtLeftEntries mergeAtRightEntries
    rw [show left.base + left.len.toNat = right.base by
      simpa only [PendingRun.endIndex] using hpairGeometry.adjacent]
  have hpairPerm :
      (sortSliceRangeEntries result.state.data left.base
        (left.len.toNat + right.len.toNat)).toList.Perm
      (sortSliceRangeEntries pre.data left.base
        (left.len.toNat + right.len.toNat)).toList := by
    rw [hprePairEntries]
    exact hselected.rangeEntriesPerm
  have hentrySnapshot := hsnapshot.preserve_mergeRange hselected.frame
    hpairStop hpairPerm
  have hconsumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
      pre.basekeys scanned := by
    apply hselected.frame.widen hpairGeometry.leftBase
    have hstop : left.base + (left.len.toNat + right.len.toNat) =
        right.endIndex := by
      have hadj : left.base + left.len.toNat = right.base := by
        simpa only [PendingRun.endIndex] using hpairGeometry.adjacent
      simp only [PendingRun.endIndex]
      omega
    rw [hstop]
    exact hpairGeometry.rightEnd
  exact
    { safety := hsafety
      selected := ⟨left, right, hselected⟩
      pendingRunsCorrect := hpendingCorrect
      entrySnapshot := hentrySnapshot
      comparator := hsafety.stableFrame.comparator.trans hcompare
      consumedFrame := hconsumedFrame }

private theorem mergeAt_correct_mergeLo
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (input : Array alpha) (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (hcorrect : PendingRunsCorrect lt input pre scanned)
    (hsnapshot : EntrySnapshotPermutation source pre.data)
    (hcompare : pre.key_compare = occurrenceComparator lt)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hposition : i + 2 = pre.pending.size ∨ i + 3 = pre.pending.size)
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hprep : MergeAtPreparationSafetyPost pre i
      (prepareMergeAtTraced? pre i) (.mergeLo call)) :
    ∃ result, MergeAtCorrectnessPost lt input source pre scanned i result := by
  have hprepare : prepareMergeAt? pre i = some (.mergeLo call) := by
    calc
      prepareMergeAt? pre i = (prepareMergeAtTraced? pre i).erase :=
        hprep.exactErasure.symm
      _ = (prepareMergeAtTraced? pre i).result := rfl
      _ = some (.mergeLo call) := hprep.resultEq
  have hcallComparator : call.state.key_compare = occurrenceComparator lt := by
    have hframe : call.state.key_compare = pre.key_compare := by
      simpa [MergeAtPreparation.state] using hprep.stableFrame.comparator
    exact hframe.trans hcompare
  have hgeometry := mergeLo_callsite_safety_geometry pre scanned i call
    hcorrect.layout hmax hprepare
  have hcallPre := mergeAtCall_correctnessPre horder hcorrect hmax
    (prepareMergeAt_lo_callsite_of_eq_some pre i call hprepare).1 hgeometry
    hcallComparator
  let trimmedCanonical : List (Occurrence alpha) :=
    (sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList
  rcases mergeLo_correct horder trimmedCanonical pre scanned i call
      hcorrect.layout hmax hprepare hInv hLive hMode hcallComparator
      hcallPre.trimmedStable hcallPre.semantic with
    ⟨loResult, hlo⟩
  have hlocalExact :
      (sortSliceRangeEntries loResult.state.data call.ssa.toNat
        (call.na + call.nb)).toList =
      stableEntryMerge lt
        (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList
        (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList := by
    simpa [mergeLoTargetEntries, mergeLoLeftEntries, mergeLoRightEntries] using
      hlo.exactRange
  have hlift := mergeAtCall_lift_full_pair horder hcallPre hlocalExact hlo.frame
  rcases mergeAt_safe pre scanned i hcorrect.layout hmax hposition hInv hLive
      hMode with ⟨result, hsafety⟩
  have hmerge : mergeAt? pre i = some result := by
    rw [← hsafety.exactErasure]
    exact hsafety.resultEq
  have hfinish : finishMergeAtPreparation? (.mergeLo call) = some result := by
    unfold mergeAt? at hmerge
    rw [hprepare, mergeAt_bindOptionAcross_some] at hmerge
    exact hmerge
  have hresultEq : result =
      ({ state := loResult.state
         returnCode := loResult.returnCode
         fuelExhausted := loResult.fuelExhausted } :
        MergeAtResult (Occurrence alpha) nu) := by
    simp only [finishMergeAtPreparation?, hlo.safety.rawResultEq,
      fromMergeLo_eq, Option.some.injEq] at hfinish
    exact hfinish.symm
  subst result
  rcases mergeAt_preserves_pendingLayout pre scanned i
      ({ state := loResult.state
         returnCode := loResult.returnCode
         fuelExhausted := loResult.fuelExhausted } :
        MergeAtResult (Occurrence alpha) nu)
      hcorrect.layout hmerge with
    ⟨before, left, right, after, hbeforeLength, hbeforePending,
      hafterPending, _hleftNN, _hleftPos, _hrightNN, _hrightPos,
      _hadjacent, hcombinedLength, _hlayout⟩
  have hactualLeft : pre.pending[i]? = some left := by
    rw [← Array.getElem?_toList, hbeforePending, ← hbeforeLength]
    simp
  have hleftEq : left = call.left :=
    Option.some.inj (hactualLeft.symm.trans hcallPre.evidence.leftSelected)
  have hrightEq : right = call.right := by
    have hselectedRight := hcallPre.evidence.rightSelected
    have hactualRight : pre.pending[i + 1]? = some right := by
      rw [← Array.getElem?_toList, hbeforePending, ← hbeforeLength]
      simp
    exact Option.some.inj (hactualRight.symm.trans hselectedRight)
  subst left
  subst right
  have hpendingSplice : ∃ before after,
      before.length = i ∧
      pre.pending.toList = before ++ call.left :: call.right :: after ∧
      loResult.state.pending.toList =
        before ++
          ({ call.left with len := call.left.len + call.right.len } :
            PendingRun) :: after :=
    ⟨before, after, hbeforeLength, hbeforePending, hafterPending⟩
  have hselected : MergeAtSelectedPairCorrectness lt pre i
      ({ state := loResult.state
         returnCode := loResult.returnCode
         fuelExhausted := loResult.fuelExhausted } :
        MergeAtResult (Occurrence alpha) nu) call.left call.right :=
    mergeAtSelectedPairCorrectness_of_exactRange horder
    hcallPre.evidence.leftSelected hcallPre.evidence.rightSelected
    hpendingSplice hcombinedLength hcallPre.leftFullSorted
    hcallPre.rightFullSorted (by
      simpa [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
        mergeAtLeftEntries, mergeAtRightEntries, sortSliceRangeKeys] using
        hcallPre.fullStable) hlift.1 hlift.2
  exact ⟨_, mergeAtCorrectnessPost_of_selected hcorrect hsnapshot hcompare
    hsafety hselected⟩

private theorem mergeAt_correct_mergeHi
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (input : Array alpha) (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (hcorrect : PendingRunsCorrect lt input pre scanned)
    (hsnapshot : EntrySnapshotPermutation source pre.data)
    (hcompare : pre.key_compare = occurrenceComparator lt)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hposition : i + 2 = pre.pending.size ∨ i + 3 = pre.pending.size)
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hprep : MergeAtPreparationSafetyPost pre i
      (prepareMergeAtTraced? pre i) (.mergeHi call)) :
    ∃ result, MergeAtCorrectnessPost lt input source pre scanned i result := by
  have hprepare : prepareMergeAt? pre i = some (.mergeHi call) := by
    calc
      prepareMergeAt? pre i = (prepareMergeAtTraced? pre i).erase :=
        hprep.exactErasure.symm
      _ = (prepareMergeAtTraced? pre i).result := rfl
      _ = some (.mergeHi call) := hprep.resultEq
  have hcallComparator : call.state.key_compare = occurrenceComparator lt := by
    have hframe : call.state.key_compare = pre.key_compare := by
      simpa [MergeAtPreparation.state] using hprep.stableFrame.comparator
    exact hframe.trans hcompare
  have hgeometry := mergeHi_callsite_safety_geometry pre scanned i call
    hcorrect.layout hmax hprepare
  have hcallPre := mergeAtCall_correctnessPre horder hcorrect hmax
    (prepareMergeAt_hi_callsite_of_eq_some pre i call hprepare).1 hgeometry
    hcallComparator
  let trimmedCanonical : List (Occurrence alpha) :=
    (sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList
  rcases mergeHi_correct horder trimmedCanonical pre scanned i call
      hcorrect.layout hmax hprepare hInv hLive hMode hcallComparator
      hcallPre.trimmedStable hcallPre.semantic with
    ⟨hiResult, hhi⟩
  have hlocalExact :
      (sortSliceRangeEntries hiResult.state.data call.ssa.toNat
        (call.na + call.nb)).toList =
      stableEntryMerge lt
        (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList
        (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList := by
    simpa [mergeHiTargetEntries, mergeHiLeftEntries, mergeHiRightEntries] using
      hhi.exactRange
  have hlift := mergeAtCall_lift_full_pair horder hcallPre hlocalExact hhi.frame
  rcases mergeAt_safe pre scanned i hcorrect.layout hmax hposition hInv hLive
      hMode with ⟨result, hsafety⟩
  have hmerge : mergeAt? pre i = some result := by
    rw [← hsafety.exactErasure]
    exact hsafety.resultEq
  have hfinish : finishMergeAtPreparation? (.mergeHi call) = some result := by
    unfold mergeAt? at hmerge
    rw [hprepare, mergeAt_bindOptionAcross_some] at hmerge
    exact hmerge
  have hresultEq : result =
      ({ state := hiResult.state
         returnCode := hiResult.returnCode
         fuelExhausted := hiResult.fuelExhausted } :
        MergeAtResult (Occurrence alpha) nu) := by
    simp only [finishMergeAtPreparation?, hhi.safety.rawResultEq,
      fromMergeHi_eq, Option.some.injEq] at hfinish
    exact hfinish.symm
  subst result
  rcases mergeAt_preserves_pendingLayout pre scanned i
      ({ state := hiResult.state
         returnCode := hiResult.returnCode
         fuelExhausted := hiResult.fuelExhausted } :
        MergeAtResult (Occurrence alpha) nu)
      hcorrect.layout hmerge with
    ⟨before, left, right, after, hbeforeLength, hbeforePending,
      hafterPending, _hleftNN, _hleftPos, _hrightNN, _hrightPos,
      _hadjacent, hcombinedLength, _hlayout⟩
  have hactualLeft : pre.pending[i]? = some left := by
    rw [← Array.getElem?_toList, hbeforePending, ← hbeforeLength]
    simp
  have hleftEq : left = call.left :=
    Option.some.inj (hactualLeft.symm.trans hcallPre.evidence.leftSelected)
  have hactualRight : pre.pending[i + 1]? = some right := by
    rw [← Array.getElem?_toList, hbeforePending, ← hbeforeLength]
    simp
  have hrightEq : right = call.right :=
    Option.some.inj (hactualRight.symm.trans hcallPre.evidence.rightSelected)
  subst left
  subst right
  have hpendingSplice : ∃ before after,
      before.length = i ∧
      pre.pending.toList = before ++ call.left :: call.right :: after ∧
      hiResult.state.pending.toList =
        before ++
          ({ call.left with len := call.left.len + call.right.len } :
            PendingRun) :: after :=
    ⟨before, after, hbeforeLength, hbeforePending, hafterPending⟩
  have hselected : MergeAtSelectedPairCorrectness lt pre i
      ({ state := hiResult.state
         returnCode := hiResult.returnCode
         fuelExhausted := hiResult.fuelExhausted } :
        MergeAtResult (Occurrence alpha) nu) call.left call.right :=
    mergeAtSelectedPairCorrectness_of_exactRange horder
      hcallPre.evidence.leftSelected hcallPre.evidence.rightSelected
      hpendingSplice hcombinedLength hcallPre.leftFullSorted
      hcallPre.rightFullSorted (by
        simpa [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
          mergeAtLeftEntries, mergeAtRightEntries, sortSliceRangeKeys] using
          hcallPre.fullStable) hlift.1 hlift.2
  exact ⟨_, mergeAtCorrectnessPost_of_selected hcorrect hsnapshot hcompare
    hsafety hselected⟩

set_option maxHeartbeats 5000000 in
-- The proof follows both nested gallops and every early-return branch.
set_option maxRecDepth 10000 in
private theorem prepareMergeAt_finished_target
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {input : Array alpha}
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (early : MergeAtResult (Occurrence alpha) nu)
    (hcorrect : PendingRunsCorrect lt input pre scanned)
    (hcompare : pre.key_compare = occurrenceComparator lt)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.finished early))
    (hreturn : early.returnCode = 0)
    (hfuel : early.fuelExhausted = false) :
    ∃ left right,
      pre.pending[i]? = some left ∧
      pre.pending[i + 1]? = some right ∧
      early.state.data = pre.data ∧
      mergeAtTargetEntries lt pre left right =
        mergeAtLeftEntries pre left ++ mergeAtRightEntries pre right := by
  unfold prepareMergeAt? at hprepare
  split at hprepare
  · rename_i hposition
    have hi : i < pre.pending.size := by omega
    have hiOne : i + 1 < pre.pending.size := by omega
    let left := pre.pending[i]
    let right := pre.pending[i + 1]
    have hleft : pre.pending[i]? = some left := by
      exact Array.getElem?_eq_getElem hi
    have hright : pre.pending[i + 1]? = some right := by
      exact Array.getElem?_eq_getElem hiOne
    have hgeometry := hcorrect.layout.adjacentPair_geometry hleft hright
    have hdataStop : pre.basekeys + scanned ≤ pre.data.entries.size := by
      have hscan : pre.basekeys + scanned ≤
          pre.basekeys + pre.listlen.toNat := by
        exact Nat.add_le_add_left hcorrect.layout.2.2.1 pre.basekeys
      exact hscan.trans hcorrect.layout.2.1
    have hrightStop : right.base + right.len.toNat ≤ pre.data.entries.size := by
      exact hgeometry.rightEnd.trans hdataStop
    have hleftStop : left.base + left.len.toNat ≤ pre.data.entries.size := by
      calc
        left.base + left.len.toNat = right.base := by
          simpa only [PendingRun.endIndex] using hgeometry.adjacent
        _ ≤ right.base + right.len.toNat := by omega
        _ ≤ pre.data.entries.size := hrightStop
    have hleftMax : left.len.toNat ≤ PY_LIST_MAX := by
      calc
        left.len.toNat ≤ left.len.toNat + right.len.toNat := by omega
        _ ≤ scanned := hgeometry.pairSpan
        _ ≤ pre.listlen.toNat := hgeometry.scannedBound
        _ ≤ PY_LIST_MAX := hmax
    have hrightMax : right.len.toNat ≤ PY_LIST_MAX := by
      calc
        right.len.toNat ≤ left.len.toNat + right.len.toNat := by omega
        _ ≤ scanned := hgeometry.pairSpan
        _ ≤ pre.listlen.toNat := hgeometry.scannedBound
        _ ≤ PY_LIST_MAX := hmax
    rcases Array.exists_pair_split_of_getElem?_eq_some hleft hright with
      ⟨before, after, _hbeforeLength, hpendingSplit⟩
    have hleftMember : left ∈ pre.pending.toList := by
      rw [hpendingSplit]
      simp
    have hrightMember : right ∈ pre.pending.toList := by
      rw [hpendingSplit]
      simp
    have hleftSorted : Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys pre.data left.base left.len.toNat) := by
      simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
        hcorrect.runSorted left hleftMember
    have hrightSorted : Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys pre.data right.base right.len.toNat) := by
      simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
        hcorrect.runSorted right hrightMember
    let call : MergeState (Occurrence alpha) nu :=
      { pre with
        pending :=
          (pre.pending.setIfInBounds i
            { left with len := left.len + right.len }).eraseIdxIfInBounds
              (i + 1) }
    have hcallCompare : call.key_compare = occurrenceComparator lt := by
      simpa [call] using hcompare
    rw [hleft, mergeAt_bindOptionAcross_some, hright,
      mergeAt_bindOptionAcross_some] at hprepare
    split at hprepare
    · rename_i _hguard
      rw [combinePendingAt_eq] at hprepare
      dsimp only at hprepare
      split at hprepare
      · simp at hprepare
      · rename_i _firstRead firstB hfirstB
        generalize hgallopRight : gallopRight? _ _ _ _ _ _ =
          gallopRightResult at hprepare
        cases gallopRightResult with
        | none =>
            rw [mergeAt_bindOptionAcross_none] at hprepare
            simp at hprepare
        | some trimA =>
            rw [mergeAt_bindOptionAcross_some] at hprepare
            have hgallopRightCall : gallopRight? call pre.data
                (Int.ofNat left.base) firstB.key left.len.toNat 0 =
                some trimA := by
              simpa [call] using hgallopRight
            by_cases hfuelA : trimA.fuelExhausted = true
            · rw [if_pos hfuelA] at hprepare
              simp only [Option.some.injEq,
                MergeAtPreparation.finished.injEq] at hprepare
              subst early
              norm_num at hreturn
            · rw [if_neg hfuelA] at hprepare
              by_cases hpastA : left.len.toNat < trimA.index
              · rw [if_pos hpastA] at hprepare
                simp at hprepare
              · rw [if_neg hpastA] at hprepare
                by_cases hnaZero : left.len.toNat - trimA.index = 0
                · rw [if_pos hnaZero] at hprepare
                  simp only [Option.some.injEq,
                    MergeAtPreparation.finished.injEq] at hprepare
                  subst early
                  refine ⟨left, right, hleft, hright, rfl, ?_⟩
                  have hend : trimA.index = left.len.toNat := by omega
                  simpa only [mergeAtTargetEntries, mergeAtLeftEntries,
                    mergeAtRightEntries] using
                    (stableEntryMerge_eq_append_of_gallopRight_end horder call
                      pre.data left.base left.len.toNat right.base
                      right.len.toNat firstB trimA hcallCompare hleftStop
                      hrightStop hleftSorted hgeometry.leftPositive
                      hgeometry.rightPositive hleftMax hfirstB
                      hgallopRightCall hend)
                · rw [if_neg hnaZero] at hprepare
                  generalize hlastA : pre.data.read?
                    (Int.ofNat (left.base + trimA.index +
                      (left.len.toNat - trimA.index) - 1)) = lastAResult at hprepare
                  cases lastAResult with
                  | none => simp at hprepare
                  | some lastA =>
                      dsimp only at hprepare
                      generalize hgallopLeft : gallopLeft? _ _ _ _ _ _ =
                        gallopLeftResult at hprepare
                      cases gallopLeftResult with
                      | none =>
                          rw [mergeAt_bindOptionAcross_none] at hprepare
                          simp at hprepare
                      | some trimB =>
                          rw [mergeAt_bindOptionAcross_some] at hprepare
                          have hgallopLeftCall : gallopLeft? call pre.data
                              (Int.ofNat right.base) lastA.key
                              right.len.toNat (right.len.toNat - 1) =
                              some trimB := by
                            simpa [call] using hgallopLeft
                          by_cases hfuelB : trimB.fuelExhausted = true
                          · rw [if_pos hfuelB] at hprepare
                            simp only [Option.some.injEq,
                              MergeAtPreparation.finished.injEq] at hprepare
                            subst early
                            norm_num at hreturn
                          · rw [if_neg hfuelB] at hprepare
                            by_cases hpastB : right.len.toNat < trimB.index
                            · rw [if_pos hpastB] at hprepare
                              simp at hprepare
                            · rw [if_neg hpastB] at hprepare
                              by_cases hnbZero : trimB.index = 0
                              · exfalso
                                exact mergeAt_secondTrimZero_impossible horder
                                  call pre.data left.base left.len.toNat
                                  right.base right.len.toNat firstB lastA trimA
                                  trimB hcallCompare hleftStop hrightStop
                                  hleftSorted hrightSorted hgeometry.leftPositive
                                  hgeometry.rightPositive hleftMax hrightMax
                                  hfirstB hgallopRightCall (by omega) hlastA
                                  hgallopLeftCall hnbZero
                              · rw [if_neg hnbZero] at hprepare
                                by_cases hlo :
                                    left.len.toNat - trimA.index ≤ trimB.index
                                · rw [if_pos hlo] at hprepare
                                  simp at hprepare
                                · rw [if_neg hlo] at hprepare
                                  simp at hprepare
    · simp at hprepare
  · simp at hprepare

set_option maxHeartbeats 5000000 in
-- Closing the early branch reconstructs the global pending stability proof.
private theorem mergeAt_correct_finished
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (input : Array alpha) (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (early : MergeAtResult (Occurrence alpha) nu)
    (hcorrect : PendingRunsCorrect lt input pre scanned)
    (hsnapshot : EntrySnapshotPermutation source pre.data)
    (hcompare : pre.key_compare = occurrenceComparator lt)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hposition : i + 2 = pre.pending.size ∨ i + 3 = pre.pending.size)
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hprep : MergeAtPreparationSafetyPost pre i
      (prepareMergeAtTraced? pre i) (.finished early)) :
    ∃ result, MergeAtCorrectnessPost lt input source pre scanned i result := by
  have hprepare : prepareMergeAt? pre i = some (.finished early) := by
    calc
      prepareMergeAt? pre i = (prepareMergeAtTraced? pre i).erase :=
        hprep.exactErasure.symm
      _ = (prepareMergeAtTraced? pre i).result := rfl
      _ = some (.finished early) := hprep.resultEq
  have hsuccess := hprep.finishedSuccess early rfl
  rcases prepareMergeAt_finished_target horder pre scanned i early hcorrect
      hcompare hmax hprepare hsuccess.1 hsuccess.2 with
    ⟨selectedLeft, selectedRight, hselectedLeft, hselectedRight,
      hearlyData, htarget⟩
  rcases mergeAt_safe pre scanned i hcorrect.layout hmax hposition hInv hLive
      hMode with ⟨result, hsafety⟩
  have hmerge : mergeAt? pre i = some result := by
    rw [← hsafety.exactErasure]
    exact hsafety.resultEq
  have hresultEq : result = early := by
    unfold mergeAt? at hmerge
    rw [hprepare, mergeAt_bindOptionAcross_some] at hmerge
    change some early = some result at hmerge
    exact (Option.some.inj hmerge).symm
  subst result
  rcases mergeAt_preserves_pendingLayout pre scanned i early
      hcorrect.layout hmerge with
    ⟨before, left, right, after, hbeforeLength, hbeforePending,
      hafterPending, _hleftNN, _hleftPos, _hrightNN, _hrightPos,
      _hadjacent, hcombinedLength, _hlayout⟩
  have hactualLeft : pre.pending[i]? = some left := by
    rw [← Array.getElem?_toList, hbeforePending, ← hbeforeLength]
    simp
  have hleftEq : left = selectedLeft :=
    Option.some.inj (hactualLeft.symm.trans hselectedLeft)
  subst selectedLeft
  have hactualRight : pre.pending[i + 1]? = some right := by
    rw [← Array.getElem?_toList, hbeforePending, ← hbeforeLength]
    simp
  have hrightEq : right = selectedRight :=
    Option.some.inj (hactualRight.symm.trans hselectedRight)
  subst selectedRight
  have hleftMember : left ∈ pre.pending.toList := by
    rw [hbeforePending]
    simp
  have hrightMember : right ∈ pre.pending.toList := by
    rw [hbeforePending]
    simp
  have hleftSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys pre.data left.base left.len.toNat) := by
    simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
      hcorrect.runSorted left hleftMember
  have hrightSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys pre.data right.base right.len.toNat) := by
    simpa only [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using
      hcorrect.runSorted right hrightMember
  have hglobalDecomposition :=
    pendingOccurrenceKeys_pair_decomposition hbeforePending
  have hfullSublist :
      ((pendingRunOccurrenceKeys pre left).toList ++
        (pendingRunOccurrenceKeys pre right).toList).Sublist
          (pendingOccurrenceKeys pre) := by
    rw [hglobalDecomposition]
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using
      (((List.nil_sublist (pendingOccurrenceKeysOf pre before)).append
        ((List.Sublist.refl
          (pendingRunOccurrenceKeys pre left).toList).append
          (List.Sublist.refl
            (pendingRunOccurrenceKeys pre right).toList))).append
        (List.nil_sublist (pendingOccurrenceKeysOf pre after)))
  have hfullStable : StableOccurrencePermutation lt
      ((pendingRunOccurrenceKeys pre left).toList ++
        (pendingRunOccurrenceKeys pre right).toList)
      ((pendingRunOccurrenceKeys pre left).toList ++
        (pendingRunOccurrenceKeys pre right).toList) :=
    ⟨List.Perm.refl _, hcorrect.pending_stable.sublist hfullSublist⟩
  have hpairGeometry := hcorrect.layout.adjacentPair_geometry
    hactualLeft hactualRight
  have hprePair :
      (sortSliceRangeEntries pre.data left.base
        (left.len.toNat + right.len.toNat)).toList =
      mergeAtLeftEntries pre left ++ mergeAtRightEntries pre right := by
    rw [sortSliceRangeEntries_toList_add]
    unfold mergeAtLeftEntries mergeAtRightEntries
    rw [show left.base + left.len.toNat = right.base by
      simpa only [PendingRun.endIndex] using hpairGeometry.adjacent]
  have hexact :
      (sortSliceRangeEntries early.state.data left.base
        (left.len.toNat + right.len.toNat)).toList =
      mergeAtTargetEntries lt pre left right := by
    rw [hearlyData, hprePair]
    exact htarget.symm
  have hframe : SortSlice.EqualOutsideRange pre.data early.state.data
      left.base (left.len.toNat + right.len.toNat) :=
    SortSlice.EqualOutsideRange.of_eq hearlyData.symm _ _
  have hpendingSplice : ∃ before after,
      before.length = i ∧
      pre.pending.toList = before ++ left :: right :: after ∧
      early.state.pending.toList =
        before ++
          ({ left with len := left.len + right.len } : PendingRun) :: after :=
    ⟨before, after, hbeforeLength, hbeforePending, hafterPending⟩
  have hselected : MergeAtSelectedPairCorrectness lt pre i early left right :=
    mergeAtSelectedPairCorrectness_of_exactRange horder hactualLeft
      hactualRight hpendingSplice hcombinedLength hleftSorted hrightSorted
      (by
        simpa [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
          mergeAtLeftEntries, mergeAtRightEntries, sortSliceRangeKeys] using
          hfullStable) hexact hframe
  exact ⟨early, mergeAtCorrectnessPost_of_selected hcorrect hsnapshot hcompare
    hsafety hselected⟩

/-- End-to-end functional correctness of the source-admitted `merge_at`
call.  Every premise is either a scan invariant, source position guard,
storage invariant, or the strict weak order required by stable merging. -/
theorem mergeAt_correct
    {lt : BoolComparator alpha}
    (horder : BoolStrictWeakOrder lt)
    (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu)
    (scanned i : Nat)
    (hcorrect : PendingRunsCorrect lt input pre scanned)
    (hsnapshot : EntrySnapshotPermutation source pre.data)
    (hcompare : pre.key_compare = occurrenceComparator lt)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hposition : i + 2 = pre.pending.size ∨ i + 3 = pre.pending.size)
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ result, MergeAtCorrectnessPost lt input source pre scanned i result := by
  rcases prepareMergeAtTraced_safe pre scanned i hcorrect.layout hmax hposition
      hInv hLive hMode with ⟨prepared, hprep⟩
  cases prepared with
  | finished early =>
      exact mergeAt_correct_finished horder input source pre scanned i early
        hcorrect hsnapshot hcompare hmax hposition hInv hLive hMode hprep
  | mergeLo call =>
      exact mergeAt_correct_mergeLo horder input source pre scanned i call
        hcorrect hsnapshot hcompare hmax hposition hInv hLive hMode hprep
  | mergeHi call =>
      exact mergeAt_correct_mergeHi horder input source pre scanned i call
        hcorrect hsnapshot hcompare hmax hposition hInv hLive hMode hprep

/-! ## Executable branch regressions -/

/-- Compact observable tag for the three preparation outcomes.  Tags zero,
one, and two denote finished, `merge_lo`, and `merge_hi`, respectively. -/
private def mergeAtPreparationObservation (prepared : MergeAtPreparation Nat Nat) :
    Nat × Int × Bool × Nat × Nat :=
  match prepared with
  | .finished result =>
      (0, result.returnCode, result.fuelExhausted, 0, 0)
  | .mergeLo call =>
      (1, 0, false, call.na, call.nb)
  | .mergeHi call =>
      (2, 0, false, call.na, call.nb)

private def mergeAtEarlyLeftExhaustionRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 4 },
        { base := 1, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeAtLoBranchRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 5
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 2, value := none },
            { key := 4, value := none },
            { key := 1, value := none },
            { key := 3, value := none },
            { key := 5, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 2, power := some 4 },
        { base := 2, len := 3, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeAtHiBranchRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 3, value := none },
            { key := 5, value := none },
            { key := 7, value := none },
            { key := 2, value := none },
            { key := 6, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 4, power := some 4 },
        { base := 4, len := 2, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeAtThirdLastSlideRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none },
            { key := 3, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 4 },
        { base := 1, len := 1, power := some 7 },
        { base := 2, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Deliberately inconsistent comparator: the first gallop retains all of A,
but the second gallop returns zero. -/
private def mergeAtSecondTrimZeroRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 3, value := none },
            { key := 2, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 2, power := some 4 },
        { base := 2, len := 1, power := none }]
    key_compare := fun left right => decide (left = 2 ∧ right = 1)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in
/-- Concrete execution reaches the successful early return where the first
gallop consumes all of the left run. -/
theorem mergeAt_earlyLeftExhaustion_regression :
    gallopRight? mergeAtEarlyLeftExhaustionRegressionState
        mergeAtEarlyLeftExhaustionRegressionState.data 0 2 1 0 =
      some { index := 1, fuelExhausted := false } ∧
    (prepareMergeAt? mergeAtEarlyLeftExhaustionRegressionState 0).map
        mergeAtPreparationObservation =
      some (0, 0, false, 0, 0) := by
  decide

set_option linter.style.nativeDecide false in
/-- Concrete execution reaches the nonempty `merge_lo` continuation. -/
theorem mergeAt_mergeLo_branch_regression :
    (prepareMergeAt? mergeAtLoBranchRegressionState 0).map
        mergeAtPreparationObservation =
      some (1, 0, false, 2, 2) := by
  decide

set_option linter.style.nativeDecide false in
/-- Concrete execution reaches the strict complementary `merge_hi`
continuation. -/
theorem mergeAt_mergeHi_branch_regression :
    (prepareMergeAt? mergeAtHiBranchRegressionState 0).map
        mergeAtPreparationObservation =
      some (2, 0, false, 3, 2) := by
  decide

set_option linter.style.nativeDecide false in
/-- Concrete third-last execution both merges the selected pair and slides the
unrelated last run into the vacated slot. -/
theorem mergeAt_thirdLast_slide_regression :
    (mergeAt? mergeAtThirdLastSlideRegressionState 0).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList)) =
      some
        (0, false,
          [{ base := 0, len := 2, power := some 4 },
           { base := 2, len := 1, power := none }]) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The inconsistent comparator makes the first trim zero and the second trim
zero, and the raw preparation observably takes CPython's defensive successful
second-trim-zero branch. -/
theorem mergeAt_inconsistentComparator_secondTrimZero_regression :
    mergeAtSecondTrimZeroRegressionState.key_compare 2 1 = true ∧
    gallopRight? mergeAtSecondTrimZeroRegressionState
        mergeAtSecondTrimZeroRegressionState.data 0 2 2 0 =
      some { index := 0, fuelExhausted := false } ∧
    gallopLeft? mergeAtSecondTrimZeroRegressionState
        mergeAtSecondTrimZeroRegressionState.data 2 3 1 0 =
      some { index := 0, fuelExhausted := false } ∧
    (prepareMergeAt? mergeAtSecondTrimZeroRegressionState 0).map
        mergeAtPreparationObservation =
      some (0, 0, false, 0, 0) := by
  decide

end CPythonListsort

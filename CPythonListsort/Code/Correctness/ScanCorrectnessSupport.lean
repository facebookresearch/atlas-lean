/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.ScanRemainder
import Code.Policy.MergeTopPowerPreservation

/-!
# Support lemmas for forward scan correctness

This module collects comparator-independent range and frame lemmas, together
with the absolute-origin stability composition used by the forward scan proof.
It deliberately does not state the scan-step theorem itself.
-/

namespace CPythonListsort

universe u v

/-- An absolute-origin canonical segment splits at an adjacent subrange
boundary. -/
theorem canonicalOccurrenceSegment_add (input : Array α) (base left right : Nat) :
    canonicalOccurrenceSegment input base (left + right) =
      canonicalOccurrenceSegment input base left ++
        canonicalOccurrenceSegment input (base + left) right := by
  simp [canonicalOccurrenceSegment, List.extract, List.take_add, List.drop_drop]

/-- Absolute tagging makes every canonical segment pairwise stable relative to
itself: later list positions have strictly later absolute origins. -/
theorem canonicalOccurrenceSegment_pairwise_stable
    (lt : BoolComparator α) (input : Array α) (base count : Nat) :
    (canonicalOccurrenceSegment input base count).Pairwise fun earlier later =>
      ComparatorEquivalent lt earlier.value later.value →
        earlier.origin < later.origin := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij _
  simp [canonicalOccurrenceSegment, tagOccurrences] at hi hj ⊢
  omega

/-- Stable permutations of two adjacent absolute-origin segments append to a
stable permutation of their union.  Cross-segment comparator-equivalent pairs
are stable because every origin in the left segment is strictly before every
origin in the right segment. -/
theorem stableOccurrencePermutation_append_adjacent
    {lt : BoolComparator α} {input : Array α}
    {base leftCount rightCount : Nat}
    {left right : List (Occurrence α)}
    (hleft : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input base leftCount) left)
    (hright : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input (base + leftCount) rightCount) right) :
    StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input base (leftCount + rightCount))
      (left ++ right) := by
  rw [canonicalOccurrenceSegment_add]
  refine ⟨hleft.1.append hright.1, ?_⟩
  apply List.pairwise_append.mpr
  refine ⟨hleft.2, hright.2, ?_⟩
  have hcanonical :
      (canonicalOccurrenceSegment input base leftCount ++
        canonicalOccurrenceSegment input (base + leftCount) rightCount).Pairwise
          (fun earlier later =>
            ComparatorEquivalent lt earlier.value later.value →
              earlier.origin < later.origin) := by
    rw [← canonicalOccurrenceSegment_add]
    exact canonicalOccurrenceSegment_pairwise_stable lt input base
      (leftCount + rightCount)
  have hcross := (List.pairwise_append.mp hcanonical).2.2
  intro earlier hearlier later hlater
  exact hcross earlier (hleft.1.mem_iff.mp hearlier)
    later (hright.1.mem_iff.mp hlater)

namespace ScanRemainderEntriesMatch

/-- Restrict whole-entry remainder agreement to an initial subrange of the
still-unscanned suffix. -/
theorem prefix_entries_eq
    {source : SortSlice κ ν} {state : MergeState (Occurrence κ) ν}
    {scanned count : Nat}
    (h : ScanRemainderEntriesMatch source state scanned)
    (hcount : count ≤ state.listlen.toNat - scanned) :
    (sortSliceRangeEntries state.data (state.basekeys + scanned) count).toList =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (state.basekeys + scanned) count).toList := by
  have hprefix := congrArg (List.take count) h.entries_eq
  simpa [sortSliceRangeEntries_toList, List.take_take, Nat.min_eq_left hcount]
    using hprefix

/-- Key projection of `prefix_entries_eq`, expressed against the canonical
absolute-origin source segment used by run correctness. -/
theorem prefix_keys_eq
    {source : SortSlice κ ν} {state : MergeState (Occurrence κ) ν}
    {scanned count : Nat}
    (h : ScanRemainderEntriesMatch source state scanned)
    (hcount : count ≤ state.listlen.toNat - scanned) :
    (sortSliceRangeKeys state.data (state.basekeys + scanned) count).toList =
      canonicalOccurrenceSegment (source.entries.map SortSliceEntry.key)
        (state.basekeys + scanned) count := by
  have hentries := h.prefix_entries_eq hcount
  have hkeys := congrArg (List.map SortSliceEntry.key) hentries
  calc
    (sortSliceRangeKeys state.data (state.basekeys + scanned) count).toList =
        (sortSliceRangeEntries state.data
          (state.basekeys + scanned) count).toList.map SortSliceEntry.key := by
          simp [sortSliceRangeKeys]
    _ = (sortSliceRangeEntries (tagSortSliceOccurrences source)
          (state.basekeys + scanned) count).toList.map SortSliceEntry.key :=
      hkeys
    _ = canonicalOccurrenceSegment
          (source.entries.map SortSliceEntry.key)
          (state.basekeys + scanned) count := by
      rw [← Array.toList_map, ← sortSliceRangeKeys_eq_map,
        sortSliceRangeKeys_tagSortSliceOccurrences]
      rfl

end ScanRemainderEntriesMatch

namespace PendingRunsCorrect

/-- Updating only an initial part of the unscanned suffix preserves correctness
of every already-pending run.  Structural fields and the pending array are
named explicitly, so the theorem cannot silently alter the represented prefix. -/
theorem preserve_unscanned_update
    {lt : BoolComparator α} {input : Array α}
    {before after : MergeState (Occurrence α) ν}
    {scanned changed : Nat}
    (h : PendingRunsCorrect lt input before scanned)
    (hlistlen : after.listlen = before.listlen)
    (hbasekeys : after.basekeys = before.basekeys)
    (hpending : after.pending = before.pending)
    (hframe : SortSlice.EqualOutsideRange before.data after.data
      (before.basekeys + scanned) changed) :
    PendingRunsCorrect lt input after scanned := by
  have hlayout : PendingLayout after scanned := by
    have hbeforeLayout := h.layout
    unfold PendingLayout at hbeforeLayout ⊢
    rw [hlistlen, hbasekeys, hpending, ← hframe.size_eq]
    exact hbeforeLayout
  have hrunKeys : ∀ run ∈ before.pending.toList,
      pendingRunOccurrenceKeys after run =
        pendingRunOccurrenceKeys before run := by
    intro run hrun
    have hspec := h.layout.2.2.2.member_spec hrun
    have hrange := hframe.keys_eq_of_disjoint run.base run.len.toNat
      (Or.inl (by
        simp only [PendingRun.endIndex] at hspec
        exact hspec.2.2.2))
    simpa [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using hrange.symm
  have hpendingKeys : pendingOccurrenceKeys after =
      pendingOccurrenceKeys before := by
    unfold pendingOccurrenceKeys
    rw [hpending]
    apply List.flatMap_congr
    intro run hrun
    exact congrArg Array.toList (hrunKeys run hrun)
  refine ⟨hlayout, ?_, ?_⟩
  · intro run hrun
    have hrunBefore : run ∈ before.pending.toList := by
      simpa [hpending] using hrun
    rw [hrunKeys run hrunBefore]
    exact h.runSorted run hrunBefore
  · rw [hbasekeys, hpendingKeys]
    exact h.stableOccurrencePermutation

end PendingRunsCorrect

end CPythonListsort

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.ScanRemainder

/-!
# Persistent whole-entry input snapshot

The scan invariant needs more than a key-only suffix snapshot: every movement
step must keep the original key occurrence paired with its original optional
payload.  `EntrySnapshotPermutation` records that persistent whole-array fact.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- The current slice contains exactly the absolutely tagged source entries,
including their optional payloads.  This invariant deliberately ranges over
the whole array, so local correctness posts can preserve it by a frame plus a
whole-entry permutation of the modified range. -/
def EntrySnapshotPermutation (source : SortSlice κ ν)
    (current : SortSlice (Occurrence κ) ν) : Prop :=
  current.entries.toList.Perm
    (tagSortSliceOccurrences source).entries.toList

namespace EntrySnapshotPermutation

/-- Occurrence-tagging a validated input establishes the snapshot invariant
definitionally, without inspecting whether the input is keyed or unkeyed. -/
theorem with_occurrence_keys (input : ListSortInput κ ν) :
    EntrySnapshotPermutation input.slice input.withOccurrenceKeys.slice := by
  exact List.Perm.refl _

/-- Raw initialization copies the tagged source into the main data field
exactly.  This fact is independent of the comparator and values mode. -/
theorem initial_merge_state_raw
    (keyCompare : BoolComparator (Occurrence κ)) (hasKeyfunc : Bool)
    (source : SortSlice κ ν) :
    EntrySnapshotPermutation source
      (CPythonListsort.initialMergeState keyCompare hasKeyfunc
        (tagSortSliceOccurrences source)).1.data := by
  rw [CPythonListsort.initialMergeState_data]
  exact List.Perm.refl _

/-- `initialMergeState` installs the occurrence-tagged validated input as its
main data slice, so initialization establishes the persistent snapshot. -/
theorem initial_merge_state (keyCompare : BoolComparator (Occurrence κ))
    (input : ListSortInput κ ν) :
    EntrySnapshotPermutation input.slice
      (CPythonListsort.initialMergeState keyCompare input.hasKeyfunc
        input.withOccurrenceKeys.slice).1.data := by
  rw [CPythonListsort.initialMergeState_data]
  exact with_occurrence_keys input

/-- Keyed constructor specialization of `initialMergeState`. -/
theorem keyed_initial (keyCompare : BoolComparator (Occurrence κ))
    (entries : Array (κ × ν)) :
    EntrySnapshotPermutation (ListSortInput.keyed entries).slice
      (CPythonListsort.initialMergeState keyCompare true
        (ListSortInput.keyed entries).withOccurrenceKeys.slice).1.data := by
  exact initial_merge_state keyCompare (ListSortInput.keyed entries)

/-- Unkeyed constructor specialization of `initialMergeState`. -/
theorem unkeyed_initial (keyCompare : BoolComparator (Occurrence κ))
    (keys : Array κ) :
    EntrySnapshotPermutation (ListSortInput.unkeyed keys).slice
      (CPythonListsort.initialMergeState keyCompare false
        (ListSortInput.unkeyed keys).withOccurrenceKeys.slice).1.data := by
  exact initial_merge_state keyCompare (ListSortInput.unkeyed keys)

/-- A whole-array permutation step preserves the tagged source snapshot. -/
theorem preserve_of_whole_entries_perm
    {source : SortSlice κ ν}
    {before after : SortSlice (Occurrence κ) ν}
    (snapshot : EntrySnapshotPermutation source before)
    (step : after.entries.toList.Perm before.entries.toList) :
    EntrySnapshotPermutation source after :=
  step.trans snapshot

end EntrySnapshotPermutation

private theorem entries_eq_prefix_range_suffix
    (slice : SortSlice α β) (start count : Nat) :
    slice.entries.toList =
      slice.entries.toList.take start ++
        (sortSliceRangeEntries slice start count).toList ++
          slice.entries.toList.drop (start + count) := by
  rw [sortSliceRangeEntries_toList]
  conv_lhs =>
    rw [← List.take_append_drop start slice.entries.toList]
  conv_lhs =>
    rhs
    rw [← List.take_append_drop count (slice.entries.toList.drop start)]
  simp only [List.drop_drop, List.append_assoc]

/-- A framed local whole-entry permutation is a whole-array permutation.

The explicit stop bound rules out a clipped target range.  The frame supplies
the exact prefix and suffix, while `localPerm` supplies the only portion that
may be reordered. -/
theorem wholeEntries_perm_of_range_perm_and_frame
    {before after : SortSlice α β} {start count : Nat}
    (frame : SortSlice.EqualOutsideRange before after start count)
    (stop : start + count ≤ before.entries.size)
    (localPerm :
      (sortSliceRangeEntries after start count).toList.Perm
        (sortSliceRangeEntries before start count).toList) :
    after.entries.toList.Perm before.entries.toList := by
  have stopAfter : start + count ≤ after.entries.size := by
    rw [← frame.size_eq]
    exact stop
  have prefixEq :
      after.entries.toList.take start = before.entries.toList.take start := by
    have rangeEq := frame.entries_eq_of_disjoint 0 start (Or.inl (by omega))
    have listEq := congrArg Array.toList rangeEq
    simpa [sortSliceRangeEntries_toList] using listEq.symm
  have suffixEq :
      after.entries.toList.drop (start + count) =
        before.entries.toList.drop (start + count) := by
    have rangeEq := frame.entries_eq_of_disjoint
      (start + count) before.entries.size (Or.inr (by omega))
    have listEq := congrArg Array.toList rangeEq
    rw [sortSliceRangeEntries_toList, sortSliceRangeEntries_toList] at listEq
    have beforeLength : before.entries.toList.length = before.entries.size := by
      simp
    have afterLength : after.entries.toList.length = after.entries.size := by
      simp
    have takeBefore :
        (before.entries.toList.drop (start + count)).take before.entries.size =
          before.entries.toList.drop (start + count) := by
      apply List.take_of_length_le
      simp only [List.length_drop, beforeLength]
      omega
    have takeAfter :
        (after.entries.toList.drop (start + count)).take before.entries.size =
          after.entries.toList.drop (start + count) := by
      apply List.take_of_length_le
      simp only [List.length_drop, afterLength]
      rw [← frame.size_eq]
      omega
    simpa only [takeBefore, takeAfter] using listEq.symm
  rw [entries_eq_prefix_range_suffix after start count,
    entries_eq_prefix_range_suffix before start count, prefixEq, suffixEq]
  exact List.Perm.append
    (List.Perm.append (List.Perm.refl _) localPerm) (List.Perm.refl _)

namespace EntrySnapshotPermutation

/-- Preserve the persistent snapshot from the exact postconditions exported by
a local sorting step: a frame, an in-bounds range, and a whole-entry range
permutation. -/
theorem preserve_local
    {source : SortSlice κ ν}
    {before after : SortSlice (Occurrence κ) ν}
    {start count : Nat}
    (snapshot : EntrySnapshotPermutation source before)
    (frame : SortSlice.EqualOutsideRange before after start count)
    (stop : start + count ≤ before.entries.size)
    (localPerm :
      (sortSliceRangeEntries after start count).toList.Perm
        (sortSliceRangeEntries before start count).toList) :
    EntrySnapshotPermutation source after :=
  preserve_of_whole_entries_perm snapshot
    (wholeEntries_perm_of_range_perm_and_frame frame stop localPerm)

end EntrySnapshotPermutation

private def wrongPayloadKeyedInput : ListSortInput Nat Nat :=
  ListSortInput.keyed #[(1, 10), (2, 20)]

private def wrongPayloadTaggedSlice : SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 1, origin := 0 }, value := some 10 },
        { key := { value := 2, origin := 1 }, value := some 99 }] }

/-- Anti-vacuity regression: the key projections are exactly equal, while the
second keyed payload changes from `20` to `99`; that payload-only corruption
does not satisfy the whole-entry snapshot invariant. -/
theorem entrySnapshotPermutation_rejects_wrong_keyed_payload :
    wrongPayloadTaggedSlice.entries.map SortSliceEntry.key =
        (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map
          SortSliceEntry.key ∧
      wrongPayloadTaggedSlice.entries.map SortSliceEntry.value =
        #[some 10, some 99] ∧
      (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map
          SortSliceEntry.value = #[some 10, some 20] ∧
      wrongPayloadTaggedSlice.entries.map SortSliceEntry.value ≠
        (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map
          SortSliceEntry.value ∧
      ¬EntrySnapshotPermutation wrongPayloadKeyedInput.slice
        wrongPayloadTaggedSlice := by
  simp [EntrySnapshotPermutation, wrongPayloadKeyedInput,
    wrongPayloadTaggedSlice, ListSortInput.keyed, tagSortSliceOccurrences]

end CPythonListsort

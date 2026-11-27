/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.StableMerge

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Tie-direction and payload regressions -/

private def decadeLt (left right : Nat) : Bool :=
  decide (left / 10 < right / 10)

private def stableMergeLeftEquivalentEntry :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 11, origin := 3 }, value := some 110 }

private def stableMergeRightEquivalentEntry :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 19, origin := 8 }, value := some 190 }

/-- Anti-vacuity regression for the actual stability notion: the values are
unequal but comparator-equivalent.  The shared merge still selects the left
occurrence first and carries both payloads with their keys. -/
private theorem stableEntryMerge_equivalent_unequal_left_first_regression :
    stableMergeLeftEquivalentEntry.key.value ≠
        stableMergeRightEquivalentEntry.key.value ∧
      ComparatorEquivalent decadeLt
        stableMergeLeftEquivalentEntry.key.value
        stableMergeRightEquivalentEntry.key.value ∧
      stableEntryMerge decadeLt [stableMergeLeftEquivalentEntry]
          [stableMergeRightEquivalentEntry] =
        [stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry] := by
  constructor
  · decide
  constructor
  · norm_num [ComparatorEquivalent, decadeLt,
      stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry]
  · simp [stableEntryMerge, stableEntryLE, stableOccurrenceLE, decadeLt,
      stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry]

private def stableMergeLargerEntry : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 21, origin := 1 }, value := some 210 }

private def stableMergeSmallerEntry : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 11, origin := 7 }, value := some 110 }

/-- A genuinely smaller right head takes the other branch, distinguishing the
stable-equality rule from an implementation that always selects the left. -/
private theorem stableEntryMerge_strict_right_first_regression :
    stableEntryMerge decadeLt [stableMergeLargerEntry]
        [stableMergeSmallerEntry] =
      [stableMergeSmallerEntry, stableMergeLargerEntry] := by
  simp [stableEntryMerge, stableEntryLE, stableOccurrenceLE, decadeLt,
    stableMergeLargerEntry, stableMergeSmallerEntry]

end CPythonListsort

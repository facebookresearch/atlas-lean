/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.CountRunCorrectness

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Concrete semantic regressions -/

private def countRunCorrectnessOccurrence (value origin : Nat) :
    Occurrence Nat :=
  { value := value, origin := origin }

private def countRunCorrectnessEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := countRunCorrectnessOccurrence value origin
    value := some payload }

private def countRunCorrectnessState
    (slice : SortSlice (Occurrence Nat) Nat) :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := slice.entries.size
    basekeys := 0
    data := slice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def countRunCorrectnessTaggedEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 3 0 30,
        countRunCorrectnessEntry 2 1 20,
        countRunCorrectnessEntry 2 2 21,
        countRunCorrectnessEntry 1 3 10] }

/-- The two equal `2` occurrences survive the descending double reversal in
origin order `1,2`, rather than being exposed in the temporary reversed order. -/
private theorem countRun_correct_tagged_equal_block_regression :
    (countRunTraced?
      (countRunCorrectnessState countRunCorrectnessTaggedEqualSlice)
      countRunCorrectnessTaggedEqualSlice 0 4).result.map
        (fun result =>
          (result.length, result.fuelExhausted, result.slice.entries)) =
      some
        (4, false,
          #[countRunCorrectnessEntry 1 3 10,
            countRunCorrectnessEntry 2 1 20,
            countRunCorrectnessEntry 2 2 21,
            countRunCorrectnessEntry 3 0 30]) := by
  decide

private def countRunCorrectnessAllEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 2 0 20,
        countRunCorrectnessEntry 2 1 21,
        countRunCorrectnessEntry 2 2 22] }

/-- A fully equivalent run is accepted by the ascending scan and remains in
its canonical origin order. -/
private theorem countRun_correct_all_equal_regression :
    (countRunTraced?
      (countRunCorrectnessState countRunCorrectnessAllEqualSlice)
      countRunCorrectnessAllEqualSlice 0 3).result.map
        (fun result =>
          (result.length, result.fuelExhausted, result.slice.entries)) =
      some (3, false, countRunCorrectnessAllEqualSlice.entries) := by
  decide

private def countRunCorrectnessExtensionSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 3 0 30,
        countRunCorrectnessEntry 2 1 20,
        countRunCorrectnessEntry 1 2 10,
        countRunCorrectnessEntry 3 3 31,
        countRunCorrectnessEntry 4 4 40,
        countRunCorrectnessEntry 5 5 50,
        countRunCorrectnessEntry 0 6 0] }

/-- After normalizing `3,2,1`, the actual final ascending scan extends through
`3,4,5`; the two equivalent `3` occurrences remain in origin order. -/
private theorem countRun_correct_descending_then_ascending_regression :
    (countRunTraced?
      (countRunCorrectnessState countRunCorrectnessExtensionSlice)
      countRunCorrectnessExtensionSlice 0 7).result.map
        (fun result =>
          (result.length, result.fuelExhausted, result.slice.entries)) =
      some
        (6, false,
          #[countRunCorrectnessEntry 1 2 10,
            countRunCorrectnessEntry 2 1 20,
            countRunCorrectnessEntry 3 0 30,
            countRunCorrectnessEntry 3 3 31,
            countRunCorrectnessEntry 4 4 40,
            countRunCorrectnessEntry 5 5 50,
            countRunCorrectnessEntry 0 6 0]) := by
  decide

private def countRunCorrectnessNonzeroBaseSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 99 0 990,
        countRunCorrectnessEntry 3 1 30,
        countRunCorrectnessEntry 2 2 20,
        countRunCorrectnessEntry 1 3 10,
        countRunCorrectnessEntry 77 4 770] }

/-- With base one, both sentinels are untouched while exactly the selected
three-entry descending range is normalized. -/
private theorem countRun_correct_nonzero_base_frame_regression :
    (countRunTraced?
      (countRunCorrectnessState countRunCorrectnessNonzeroBaseSlice)
      countRunCorrectnessNonzeroBaseSlice 1 3).result.map
        (fun result =>
          (result.length, result.fuelExhausted, result.slice.entries)) =
      some
        (3, false,
          #[countRunCorrectnessEntry 99 0 990,
            countRunCorrectnessEntry 1 3 10,
            countRunCorrectnessEntry 2 2 20,
            countRunCorrectnessEntry 3 1 30,
            countRunCorrectnessEntry 77 4 770]) := by
  decide

end CPythonListsort

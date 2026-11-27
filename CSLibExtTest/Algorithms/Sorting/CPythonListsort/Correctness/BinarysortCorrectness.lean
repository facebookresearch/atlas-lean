/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.BinarysortCorrectness

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

private def binarysortCorrectnessNatLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def binarysortCorrectnessEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 1, origin := 0 }, value := some 10 },
        { key := { value := 1, origin := 1 }, value := some 11 },
        { key := { value := 2, origin := 2 }, value := some 20 },
        { key := { value := 1, origin := 3 }, value := some 12 }] }

private def binarysortCorrectnessEqualState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 4
    basekeys := 0
    data := binarysortCorrectnessEqualSlice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator binarysortCorrectnessNatLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Executable upper-bound regression for stability: comparison with either
older equal occurrence is false, so the actual traced search returns position
two and the actual traced sort places the new equal occurrence after both. -/
private theorem binarysort_correctness_equality_right_regression :
    (binarysortSearchTraced? 4 binarysortCorrectnessEqualState.key_compare
      binarysortCorrectnessEqualSlice 0
      { key := { value := 1, origin := 3 }, value := some 12 }
      0 3).result.map (fun result =>
        (result.position, result.fuelExhausted)) = some (2, false) ∧
    (binarysortTraced? binarysortCorrectnessEqualState
      binarysortCorrectnessEqualSlice 0 4 3).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := { value := 1, origin := 0 }, value := some 10 },
           { key := { value := 1, origin := 1 }, value := some 11 },
           { key := { value := 1, origin := 3 }, value := some 12 },
           { key := { value := 2, origin := 2 }, value := some 20 }]) := by
  decide

private def binarysortCorrectnessOffsetSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 99, origin := 90 }, value := some 900 },
        { key := { value := 2, origin := 0 }, value := some 20 },
        { key := { value := 1, origin := 1 }, value := some 10 },
        { key := { value := 2, origin := 2 }, value := some 21 },
        { key := { value := 88, origin := 91 }, value := some 800 }] }

private def binarysortCorrectnessOffsetState :
    MergeState (Occurrence Nat) Nat :=
  { binarysortCorrectnessEqualState with
    listlen := 5
    data := binarysortCorrectnessOffsetSlice }

/-- Executable nonzero-base/frame regression on the actual traced evaluator:
only `[1,4)` is sorted, both sentinel entries are unchanged, and equal keys
retain origin order inside the target range. -/
private theorem binarysort_correctness_nonzero_base_sentinel_regression :
    (binarysortTraced? binarysortCorrectnessOffsetState
      binarysortCorrectnessOffsetSlice 1 3 1).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := { value := 99, origin := 90 }, value := some 900 },
           { key := { value := 1, origin := 1 }, value := some 10 },
           { key := { value := 2, origin := 0 }, value := some 20 },
           { key := { value := 2, origin := 2 }, value := some 21 },
           { key := { value := 88, origin := 91 }, value := some 800 }]) := by
  decide

end CPythonListsort

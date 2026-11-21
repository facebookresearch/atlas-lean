/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.MergeAtCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.RuntimeAssert

namespace CPythonListsort

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

/-- Concrete execution reaches the nonempty `merge_lo` continuation. -/
theorem mergeAt_mergeLo_branch_regression :
    (prepareMergeAt? mergeAtLoBranchRegressionState 0).map
        mergeAtPreparationObservation =
      some (1, 0, false, 2, 2) := by
  decide

/-- Concrete execution reaches the strict complementary `merge_hi`
continuation. -/
theorem mergeAt_mergeHi_branch_regression :
    (prepareMergeAt? mergeAtHiBranchRegressionState 0).map
        mergeAtPreparationObservation =
      some (2, 0, false, 3, 2) := by
  decide

/-- Concrete third-last execution both merges the selected pair and slides the
unrelated last run into the vacated slot. -/
def mergeAt_thirdLast_slide_regression : IO Unit :=
  CPythonListsortTest.assertTrue "mergeAt_thirdLast_slide_regression" (decide (
    (mergeAt? mergeAtThirdLastSlideRegressionState 0).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList)) =
      some
        (0, false,
          [{ base := 0, len := 2, power := some 4 },
           { base := 2, len := 1, power := none }])))

#eval mergeAt_thirdLast_slide_regression

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

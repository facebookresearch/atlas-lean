/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.MergeHiCorrectness

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Executable exact-target regression -/

private def mergeHiCorrectnessNatLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def mergeHiCorrectnessEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := value, origin := origin }, value := some payload }

/-- A keyed fixture with one cell on each side of the affected range.  The
equal `4` occurrences straddle the two runs, so the expected stable merge also
checks the reverse-fill tie direction and whole-entry payload pairing. -/
private def mergeHiCorrectnessRegressionState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data :=
      { entries :=
          #[mergeHiCorrectnessEntry 99 0 990,
            mergeHiCorrectnessEntry 4 1 40,
            mergeHiCorrectnessEntry 5 2 50,
            mergeHiCorrectnessEntry 1 3 11,
            mergeHiCorrectnessEntry 4 4 41,
            mergeHiCorrectnessEntry 100 5 1000] }
    a :=
      { cells := Array.replicate 2 none
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := occurrenceComparator mergeHiCorrectnessNatLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- The concrete regression fixture has honest, live inline temporary storage:
its physical cell count exactly matches `alloced`. -/
private theorem mergeHi_correctness_regression_tempStorageInv :
    TempStorageInv mergeHiCorrectnessRegressionState.a
      mergeHiCorrectnessRegressionState.alloced := by
  simp only [mergeHiCorrectnessRegressionState, TempStorageInv,
    Array.size_replicate, TempStorage.multiplier, ite_eq_left]
  change 2 = (BitVec.ofNat 64 2).toNat ∧
    2 * (BitVec.ofNat 64 2).toNat ≤ MERGESTATE_TEMP_SIZE
  norm_num [BitVec.toNat_ofNat, MERGESTATE_TEMP_SIZE]

private def mergeHiCorrectnessRegressionExpectedState :
    MergeState (Occurrence Nat) Nat :=
  { mergeHiCorrectnessRegressionState with
    data :=
      { entries :=
          #[mergeHiCorrectnessEntry 99 0 990,
            mergeHiCorrectnessEntry 1 3 11,
            mergeHiCorrectnessEntry 4 1 40,
            mergeHiCorrectnessEntry 4 4 41,
            mergeHiCorrectnessEntry 5 2 50,
            mergeHiCorrectnessEntry 100 5 1000] }
    a :=
      { cells :=
          #[some (mergeHiCorrectnessEntry 1 3 11),
            some (mergeHiCorrectnessEntry 4 4 41)]
        backing := .inline
        hasValues := true } }

private def mergeHiCorrectnessRegressionExpectedResult :
    MergeHiResult (Occurrence Nat) Nat :=
  { state := mergeHiCorrectnessRegressionExpectedState
    returnCode := 0
    fuelExhausted := false }

/-- Kernel-reduced pin that the real raw evaluator reaches the concrete stable
fixture result; the public range theorem below separately checks its semantic
interpretation. -/
private theorem mergeHi_correctness_regression_evaluator :
    mergeHi? mergeHiCorrectnessRegressionState 1 3 2 2 =
      some mergeHiCorrectnessRegressionExpectedResult := by
  rfl

/-- Anti-vacuity regression for the central functional claim: the real raw
evaluator produces exactly the left-biased whole-entry merge, keeps the left
equal-key occurrence before the right one, preserves their distinct payloads,
and leaves both neighboring cells unchanged. -/
private theorem mergeHi_exact_stable_range_and_frame_regression :
    (mergeHi? mergeHiCorrectnessRegressionState 1 3 2 2).map
        (fun result =>
          ((sortSliceRangeEntries result.state.data 1 4).toList,
            result.state.data.entries[0]?, result.state.data.entries[5]?)) =
      some
        (stableEntryMerge mergeHiCorrectnessNatLt
            (sortSliceRangeEntries mergeHiCorrectnessRegressionState.data
              1 2).toList
            (sortSliceRangeEntries mergeHiCorrectnessRegressionState.data
              3 2).toList,
          some (mergeHiCorrectnessEntry 99 0 990),
          some (mergeHiCorrectnessEntry 100 5 1000)) := by
  rw [mergeHi_correctness_regression_evaluator]
  norm_num [mergeHiCorrectnessRegressionExpectedResult,
    mergeHiCorrectnessRegressionExpectedState,
    mergeHiCorrectnessRegressionState, mergeHiCorrectnessEntry,
    mergeHiCorrectnessNatLt, sortSliceRangeEntries, stableEntryMerge,
    stableEntryLE, stableOccurrenceLE]

end CPythonListsort

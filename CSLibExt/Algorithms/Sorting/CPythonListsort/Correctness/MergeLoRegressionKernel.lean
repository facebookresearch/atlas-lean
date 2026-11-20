/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeLo
import Code.Transcription.TempStorageInvariant

/-!
# Kernel-checked executable fixture for `merge_lo`

This small module keeps the closed evaluator reduction separate from the large
semantic proof module.  The exported theorem is reused there as the public
regression, so no native-code decision procedure enters the trusted proof.
-/

namespace CPythonListsort

def mergeLoCorrectnessNatLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def mergeLoCorrectnessEntry (key payload : Nat) :
    SortSliceEntry Nat Nat :=
  { key := key, value := some payload }

/-- A nonzero-base fixture with distinct payloads at an equal-key boundary,
two framed neighbors, and four allocated temporary cells. -/
def mergeLoCorrectnessRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 7
    basekeys := 0
    data :=
      { entries :=
          #[mergeLoCorrectnessEntry 99 990,
            mergeLoCorrectnessEntry 4 40,
            mergeLoCorrectnessEntry 6 60,
            mergeLoCorrectnessEntry 2 20,
            mergeLoCorrectnessEntry 4 41,
            mergeLoCorrectnessEntry 5 50,
            mergeLoCorrectnessEntry 100 1000] }
    a :=
      { cells := Array.replicate 4 none
        backing := .inline
        hasValues := true }
    alloced := 4
    pending := #[]
    key_compare := mergeLoCorrectnessNatLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Closed kernel reduction of the nonzero-base stable-tail execution. -/
theorem mergeLoCorrectnessRegression_kernel :
    (mergeLo? mergeLoCorrectnessRegressionState 1 3 2 3).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.data.entries.toList)) =
      some
        (0, false,
          [mergeLoCorrectnessEntry 99 990,
           mergeLoCorrectnessEntry 2 20,
           mergeLoCorrectnessEntry 4 40,
           mergeLoCorrectnessEntry 4 41,
           mergeLoCorrectnessEntry 5 50,
           mergeLoCorrectnessEntry 6 60,
           mergeLoCorrectnessEntry 100 1000]) := by
  decide

/-- The fixture's temporary allocation covers all four physical cells. -/
theorem mergeLoCorrectnessRegression_tempStorage_kernel :
    TempStorageInv mergeLoCorrectnessRegressionState.a
      mergeLoCorrectnessRegressionState.alloced := by
  change 4 = (4 : Nat) ∧ 2 * 4 ≤ 256
  norm_num

end CPythonListsort

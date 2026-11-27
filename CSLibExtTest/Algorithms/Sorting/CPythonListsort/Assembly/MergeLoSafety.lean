/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.MergeLoSafety
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Transcription.MergeLo

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Concrete adversarial-comparator hedge fixtures -/

/-- The concrete non-irreflexive-comparator machine used by the `mergeLo?` zero-`na`
regression satisfies the full assembly invariant, not merely the cursor arithmetic
visible in the transcription fixture. -/
theorem mergeLoNaZeroHedgeRegressionMachine_invariant :
    MergeLoMachineInvariant mergeLoNaZeroHedgeRegressionState 2 3
      mergeLoNaZeroHedgeRegressionMachine := by
  refine
    { destNonnegative := by decide
      tempAccounting := by decide
      adjacency := by decide
      rightAccounting := by decide
      mainEnd := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorage.Live]
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeLoNaZeroHedgeRegressionMachine] using
      MergeLoStableFrame.refl mergeLoNaZeroHedgeRegressionState
  · simpa [mergeLoNaZeroHedgeRegressionMachine] using
      MergeLoStorageFrame.refl mergeLoNaZeroHedgeRegressionState

/-- Changing only the comparator to strict `<` preserves the full assembly
invariant of the `merge_lo` hedge-regression geometry. -/
theorem mergeLoNaZeroHedgeStrictControlMachine_invariant :
    MergeLoMachineInvariant mergeLoNaZeroHedgeStrictControlState 2 3
      mergeLoNaZeroHedgeStrictControlMachine := by
  refine
    { destNonnegative := by decide
      tempAccounting := by decide
      adjacency := by decide
      rightAccounting := by decide
      mainEnd := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeLoNaZeroHedgeStrictControlMachine,
          mergeLoNaZeroHedgeStrictControlState,
          mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeLoNaZeroHedgeStrictControlMachine,
          mergeLoNaZeroHedgeStrictControlState,
          mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorage.Live]
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeLoNaZeroHedgeStrictControlMachine] using
      MergeLoStableFrame.refl mergeLoNaZeroHedgeStrictControlState
  · simpa [mergeLoNaZeroHedgeStrictControlMachine] using
      MergeLoStorageFrame.refl mergeLoNaZeroHedgeStrictControlState

end CPythonListsort

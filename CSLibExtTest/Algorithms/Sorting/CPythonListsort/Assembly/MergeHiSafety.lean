/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.MergeHiSafety
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Transcription.MergeHi

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Concrete adversarial-comparator hedge fixtures -/

/-- The concrete non-irreflexive-comparator cursor used by the `mergeHi?` zero-`nb`
regression satisfies the full assembly invariant, including its subtraction-sensitive
cursor geometry. -/
theorem mergeHiNbZeroHedgeRegressionCursor_invariant :
    MergeHiCursorInvariant mergeHiNbZeroHedgeRegressionState 2
      mergeHiNbZeroHedgeRegressionCursor := by
  refine
    { baseNonnegative := by decide
      ssaEquation := by decide
      ssbEquation := by decide
      destEquation := by decide
      mainRange := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorage.Live]
      requestFits := by decide
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeHiNbZeroHedgeRegressionCursor] using
      MergeHiStableFrame.refl mergeHiNbZeroHedgeRegressionState
  · simpa [mergeHiNbZeroHedgeRegressionCursor] using
      MergeHiStorageFrame.refl mergeHiNbZeroHedgeRegressionState

/-- Changing only the comparator to strict `<` preserves the full assembly
invariant of the `merge_hi` hedge-regression geometry. -/
theorem mergeHiNbZeroHedgeStrictControlCursor_invariant :
    MergeHiCursorInvariant mergeHiNbZeroHedgeStrictControlState 2
      mergeHiNbZeroHedgeStrictControlCursor := by
  refine
    { baseNonnegative := by decide
      ssaEquation := by decide
      ssbEquation := by decide
      destEquation := by decide
      mainRange := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeHiNbZeroHedgeStrictControlCursor,
          mergeHiNbZeroHedgeStrictControlState,
          mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeHiNbZeroHedgeStrictControlCursor,
          mergeHiNbZeroHedgeStrictControlState,
          mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorage.Live]
      requestFits := by decide
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeHiNbZeroHedgeStrictControlCursor] using
      MergeHiStableFrame.refl mergeHiNbZeroHedgeStrictControlState
  · simpa [mergeHiNbZeroHedgeStrictControlCursor] using
      MergeHiStorageFrame.refl mergeHiNbZeroHedgeStrictControlState

end CPythonListsort

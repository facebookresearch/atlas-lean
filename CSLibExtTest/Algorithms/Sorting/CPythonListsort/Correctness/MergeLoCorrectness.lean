/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.MergeLoCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Transcription.MergeLo

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-- The real raw evaluator resolves the equal `4` pair stably and preserves the
nonzero-base range's payload-bearing neighboring cells.  The exposed equality
does not identify which terminal branch produced that final state. -/
private theorem mergeLo_exact_stable_range_and_frame_regression :
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
  exact mergeLoCorrectnessRegression_kernel

/-- The min-gallop-one evaluator returns stable tie/payload output; this
equality observes final state, not gallop-branch entry. -/
private theorem mergeLo_correctness_gallop_tie_regression :
    (mergeLo? mergeLoGallopStabilityRegressionState 0 3 3 3).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.min_gallop, result.state.data.entries.toList)) =
      some
        (0, false, 1,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 3, value := some 30 },
           { key := 3, value := some 31 },
           { key := 4, value := some 40 },
           { key := 5, value := some 50 }]) := by
  exact mergeLo_gallop_stability_regression

end CPythonListsort

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.MergeMovementCorrectness

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Executable overlap regression -/

private def mergeMovementOverlapInput : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 3, value := some 30 },
        { key := 4, value := some 40 },
        { key := 5, value := some 50 }] }

/-- A rightward overlapping merge move reads every entry from the pre-move
snapshot; an increasing-address implementation would not produce this array. -/
private theorem mergeDataMemmove_overlap_snapshot_regression :
    mergeDataMemmove? .loCopyBTail mergeMovementOverlapInput 1 0 4 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 3, value := some 30 },
              { key := 4, value := some 40 }] } := by
  decide

end CPythonListsort

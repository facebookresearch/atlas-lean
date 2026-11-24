/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.FoundNewRun

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

private def foundNewRunExampleState : MergeState Nat Nat :=
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
      #[{ base := 0, len := 1, power := some 2 },
        { base := 1, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- The source explicitly makes an empty pending stack a no-op; in particular
it does not inspect the otherwise-invalid prospective length zero. -/
example :
    (foundNewRun?
        { foundNewRunExampleState with pending := #[] } 0).map
          (fun result =>
            (result.returnCode, result.fuelExhausted,
              result.state.pending.toList,
              result.state.data.entries.toList)) =
      some
        (0, false, [], foundNewRunExampleState.data.entries.toList) := by
  decide

/-- Collapse uses strict `>` rather than `≥`: equality leaves both runs in
place and initializes the current top run with the computed power. -/
example :
    (foundNewRun? foundNewRunExampleState 1).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList)) =
      some
        (0, false,
          [{ base := 0, len := 1, power := some 2 },
           { base := 1, len := 1, power := some 2 }]) := by
  decide

end CPythonListsort

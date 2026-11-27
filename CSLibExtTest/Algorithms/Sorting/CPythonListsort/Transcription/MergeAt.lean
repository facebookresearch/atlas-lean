/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.MergeAt
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.RuntimeAssert

namespace CPythonListsort

private def mergeAtSlideExampleState : MergeState Nat Nat :=
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

/-- When `i` is third-last, the unrelated final run slides left.  This input
also pins that trimming all of A returns only after the pending-stack update
and that the combined run retains the old left run's power. -/
def mergeAt_slide_regression : IO Unit :=
  CPythonListsortTest.assertTrue "mergeAt_slide_regression" (decide (
    (mergeAt? mergeAtSlideExampleState 0).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList)) =
      some
        (0, false,
          [{ base := 0, len := 2, power := some 4 },
           { base := 2, len := 1, power := none }])))

#eval mergeAt_slide_regression

private def mergeAtPreparationShape (prepared : MergeAtPreparation Nat Nat) :
    Option (Bool × Nat × Nat) :=
  match prepared with
  | .finished _ => none
  | .mergeLo call => some (true, call.na, call.nb)
  | .mergeHi call => some (false, call.na, call.nb)

private def mergeAtLoPreparationExampleState : MergeState Nat Nat :=
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

private def mergeAtHiPreparationExampleState : MergeState Nat Nat :=
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

/-- Concrete regression: the exposed preparation path can reach the
`merge_lo` call site with nonempty post-trim runs. -/
example :
    (prepareMergeAt? mergeAtLoPreparationExampleState 0).bind
      mergeAtPreparationShape = some (true, 2, 2) := by
  decide

/-- Concrete regression: the exposed preparation path can also reach the
strict complementary `merge_hi` call site. -/
example :
    (prepareMergeAt? mergeAtHiPreparationExampleState 0).bind
      mergeAtPreparationShape = some (false, 3, 2) := by
  decide

end CPythonListsort

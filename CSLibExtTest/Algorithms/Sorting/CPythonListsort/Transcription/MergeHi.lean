/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.MergeHi

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! The next regression uses the non-irreflexive comparator `(· ≥ ·)`.  Its
second gallop consumes the whole temporary B run, after which the real loop
dispatcher reaches `mergeHiSucceed?` through its `nb = 0` guard.  A strict-`<`
control on the identical valid geometry returns the other insertion endpoint. -/

def mergeHiNbZeroHedgeRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 99, value := some 99 },
            { key := 98, value := some 98 }] }
    a :=
      { cells :=
          #[(some { key := 1, value := some 10 }),
            (some { key := 2, value := some 20 })]
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := fun left right => decide (left ≥ right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeHiNbZeroHedgeRegressionCursor : MergeHiCursor Nat Nat :=
  { state := mergeHiNbZeroHedgeRegressionState
    dest := 2
    ssa := 0
    ssb := 1
    basea := 0
    na := 1
    nb := 2
    minGallop := MIN_GALLOP
    phase := .galloping 0 0 }

def mergeHiNbZeroHedgeStrictControlState : MergeState Nat Nat :=
  { mergeHiNbZeroHedgeRegressionState with
    key_compare := fun left right => decide (left < right) }

def mergeHiNbZeroHedgeStrictControlCursor : MergeHiCursor Nat Nat :=
  { mergeHiNbZeroHedgeRegressionCursor with
    state := mergeHiNbZeroHedgeStrictControlState }

private def mergeHiGallopStabilityRegressionState : MergeState Nat Nat :=
  { min_gallop := 1
    listlen := 7
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 2, value := some 20 },
            { key := 4, value := some 40 },
            { key := 6, value := some 60 },
            { key := 8, value := some 80 },
            { key := 1, value := some 11 },
            { key := 4, value := some 41 },
            { key := 5, value := some 51 }] }
    a :=
      { cells := Array.replicate 3 none
        backing := .inline
        hasValues := true }
    alloced := 3
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Min-gallop-one output keeps the left equal occurrence first with its
payload attached; it does not expose branch entry. -/
private theorem mergeHi_gallop_stability_regression :
    (mergeHi? mergeHiGallopStabilityRegressionState 0 4 4 3).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 1, value := some 11 },
           { key := 2, value := some 20 },
           { key := 4, value := some 40 },
           { key := 4, value := some 41 },
           { key := 5, value := some 51 },
           { key := 6, value := some 60 },
           { key := 8, value := some 80 }]) := by
  decide

/-- On one fixed cursor geometry, the non-irreflexive comparator gives
`gallop_left.index = 0`, so `bCount = nb - index` consumes all of B and reaches
the `nb = 0` success dispatch.  The strict control gives `index = nb` and a
different successful terminal path. -/
private theorem mergeHi_inconsistentComparator_nbZero_succeed_regression :
    mergeHiNbZeroHedgeRegressionState.key_compare 1 1 = true ∧
    (initializedTempPrefix? mergeHiNbZeroHedgeRegressionState.a 2).bind
        (fun temp => gallopLeft? mergeHiNbZeroHedgeRegressionState
          temp 0 3 2 1) =
      some { index := 0, fuelExhausted := false } ∧
    (initializedTempPrefix? mergeHiNbZeroHedgeStrictControlState.a 2).bind
        (fun temp => gallopLeft? mergeHiNbZeroHedgeStrictControlState
          temp 0 3 2 1) =
      some { index := 2, fuelExhausted := false } ∧
    (mergeHiGallopB? mergeHiNbZeroHedgeRegressionCursor 0
      (mergeHiLoop? 1)).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 3, value := some 30 },
           { key := 1, value := some 10 },
           { key := 2, value := some 20 }]) ∧
    (mergeHiGallopB? mergeHiNbZeroHedgeStrictControlCursor 0
      (mergeHiLoop? 1)).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 3, value := some 30 }]) := by
  decide

end CPythonListsort

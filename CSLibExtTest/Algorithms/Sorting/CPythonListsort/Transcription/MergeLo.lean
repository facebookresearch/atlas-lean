/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.MergeLo

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! The next regression deliberately uses the non-irreflexive comparator
`(· ≥ ·)`.  Its continuation always fails, so the successful result is an
observable witness that the first gallop's `index = na` result took the
`na = 0` Succeed hedge rather than continuing the round.  A strict-`<` control
on the identical geometry returns index zero and a different final ordering. -/

def mergeLoNaZeroHedgeRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 99, value := some 99 },
            { key := 98, value := some 98 },
            { key := 0, value := some 0 }] }
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

def mergeLoNaZeroHedgeRegressionMachine : MergeLoMachine Nat Nat :=
  { state := mergeLoNaZeroHedgeRegressionState
    dest := 0
    aPos := 0
    bPos := 2
    na := 2
    nb := 1
    minGallop := MIN_GALLOP }

def mergeLoNaZeroHedgeStrictControlState : MergeState Nat Nat :=
  { mergeLoNaZeroHedgeRegressionState with
    key_compare := fun left right => decide (left < right) }

def mergeLoNaZeroHedgeStrictControlMachine : MergeLoMachine Nat Nat :=
  { mergeLoNaZeroHedgeRegressionMachine with
    state := mergeLoNaZeroHedgeStrictControlState }

/-! These executable regressions pin the ordinary-mode argument order and
stable equality branch. -/

private def mergeLoStabilityRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 5
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 4, value := some 40 },
            { key := 2, value := some 20 },
            { key := 3, value := some 32 },
            { key := 3, value := some 33 }] }
    a :=
      { cells := Array.replicate 2 none
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Equal keys from the left run precede equal keys from the right run. -/
private theorem mergeLo_straight_stability_regression :
    (mergeLo? mergeLoStabilityRegressionState 0 2 2 3).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 2, value := some 20 },
           { key := 3, value := some 30 },
           { key := 3, value := some 32 },
           { key := 3, value := some 33 },
           { key := 4, value := some 40 }]) := by
  decide

def mergeLoGallopStabilityRegressionState : MergeState Nat Nat :=
  { mergeLoStabilityRegressionState with
    min_gallop := 1
    listlen := 6
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 4, value := some 40 },
            { key := 5, value := some 50 },
            { key := 1, value := some 10 },
            { key := 2, value := some 20 },
            { key := 3, value := some 31 }] }
    a :=
      { cells := Array.replicate 3 none
        backing := .inline
        hasValues := true }
    alloced := 3 }

/-- Min-gallop-one output keeps the left equal key first; it does not expose branch entry. -/
theorem mergeLo_gallop_stability_regression :
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
  decide

/-- On one fixed machine geometry, the non-irreflexive comparator gives
`gallop_right.index = na` and reaches the `na = 0` success hedge, whereas the
strict control gives index zero and a different successful terminal path. -/
private theorem mergeLo_inconsistentComparator_naZero_succeed_regression :
    mergeLoNaZeroHedgeRegressionState.key_compare 1 1 = true ∧
    ((mergeLoTempRun? mergeLoNaZeroHedgeRegressionState.a 0 2).bind
      (fun activeA => gallopRight? mergeLoNaZeroHedgeRegressionState
        activeA 0 0 2 0)) =
      some { index := 2, fuelExhausted := false } ∧
    ((mergeLoTempRun? mergeLoNaZeroHedgeStrictControlState.a 0 2).bind
      (fun activeA => gallopRight? mergeLoNaZeroHedgeStrictControlState
        activeA 0 0 2 0)) =
      some { index := 0, fuelExhausted := false } ∧
    (mergeLoGallopRound? mergeLoNaZeroHedgeRegressionMachine
      (fun _ _ _ => none)).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 0, value := some 0 }]) ∧
    (mergeLoGallopRound? mergeLoNaZeroHedgeStrictControlMachine
      (fun _ _ _ => none)).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 0, value := some 0 },
           { key := 1, value := some 10 },
           { key := 2, value := some 20 }]) := by
  decide

end CPythonListsort

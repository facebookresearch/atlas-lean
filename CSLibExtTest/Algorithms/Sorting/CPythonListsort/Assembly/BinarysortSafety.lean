/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.BinarysortSafety

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

private def binarysortRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := some 30 },
        { key := 4, value := some 40 },
        { key := 1, value := some 10 }] }

private def binarysortEqualRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 2, value := some 21 }] }

private def binarysortSingletonRegressionSlice : SortSlice Nat Nat :=
  { entries := #[{ key := 1, value := some 10 }] }

private def binarysortPairRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 2, value := some 20 },
        { key := 1, value := some 10 }] }

private def binarysortUnkeyedRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 2, value := none },
        { key := 1, value := none }] }

private def binarysortTaggedEqualRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 1, value := some 11 },
        { key := 2, value := some 20 },
        { key := 1, value := some 12 }] }

private def binarysortRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data := binarysortEqualRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def binarysortSingletonRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 1
    data := binarysortSingletonRegressionSlice }

private def binarysortPairRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 2
    data := binarysortPairRegressionSlice }

private def binarysortUnkeyedRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 2
    data := binarysortUnkeyedRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := false } }

private def binarysortTaggedEqualRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 4
    data := binarysortTaggedEqualRegressionSlice }

/-- The source normalization `ok = 0 ↦ ok = 1` makes a singleton call a
zero-iteration outer loop with an empty trace. -/
private theorem binarysort_singleton_ok_zero_regression :
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 1 0).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some (false, binarysortSingletonRegressionSlice.entries.toList) ∧
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 1 0).trace = AccessTrace.empty := by
  decide

/-- The same `ok = 0` normalization on an unsorted pair executes one complete
insertion and returns the sorted key/value pair. -/
private theorem binarysort_pair_ok_zero_regression :
    (binarysortTraced? binarysortPairRegressionState
      binarysortPairRegressionSlice 0 2 0).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 }]) ∧
    (binarysortTraced? binarysortPairRegressionState
      binarysortPairRegressionSlice 0 2 0).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 1, extent := 2 },
       { kind := .read, region := .inputKeys, index := 0, extent := 2 },
       { kind := .read, region := .inputKeys, index := 0, extent := 2 },
       { kind := .write, region := .inputKeys, index := 1, extent := 2 },
       { kind := .write, region := .inputKeys, index := 0, extent := 2 },
       { kind := .read, region := .synchronizedValues, index := 1, extent := 2 },
       { kind := .read, region := .synchronizedValues, index := 0, extent := 2 },
       { kind := .write, region := .synchronizedValues, index := 1, extent := 2 },
       { kind := .write, region := .synchronizedValues, index := 0, extent := 2 }] := by
  decide

/-- A raw-domain call whose declared range exceeds the store retains the
failed pivot-read attempt, including its actual one-cell extent. -/
private theorem binarysort_oob_attempted_read_regression :
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 2 1).result = none ∧
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 2 1).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 1, extent := 1 }] ∧
    ¬(binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 2 1).trace.allAccessesInBounds := by
  decide

/-- In the explicit no-values mode a valid full insertion emits only key-array
events; no synchronized-values event is reconstructed from entry payloads. -/
private theorem binarysort_unkeyed_no_values_trace_regression :
    (binarysortTraced? binarysortUnkeyedRegressionState
      binarysortUnkeyedRegressionSlice 0 2 0).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := 1, value := none },
           { key := 2, value := none }]) ∧
    (binarysortTraced? binarysortUnkeyedRegressionState
      binarysortUnkeyedRegressionSlice 0 2 0).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 1, extent := 2 },
       { kind := .read, region := .inputKeys, index := 0, extent := 2 },
       { kind := .read, region := .inputKeys, index := 0, extent := 2 },
       { kind := .write, region := .inputKeys, index := 1, extent := 2 },
       { kind := .write, region := .inputKeys, index := 0, extent := 2 }] := by
  decide

/-- A leftmost insertion executes the overlapping shift from the highest cell
to the lowest cell, then performs the pivot write; the complete key phase
precedes the identically ordered synchronized-values phase. -/
private theorem binarysort_insert_front_regression :
    (binarysortShiftInsertTraced? true binarysortRegressionSlice 0 2 0
      { key := 1, value := some 10 }).result.map (·.entries.toList) =
        some
          [{ key := 1, value := some 10 },
           { key := 3, value := some 30 },
           { key := 4, value := some 40 }] ∧
      (binarysortShiftInsertTraced? true binarysortRegressionSlice 0 2 0
        { key := 1, value := some 10 }).trace.accesses =
        [{ kind := .read, region := .inputKeys, index := 1, extent := 3 },
         { kind := .write, region := .inputKeys, index := 2, extent := 3 },
         { kind := .read, region := .inputKeys, index := 0, extent := 3 },
         { kind := .write, region := .inputKeys, index := 1, extent := 3 },
         { kind := .write, region := .inputKeys, index := 0, extent := 3 },
         { kind := .read, region := .synchronizedValues, index := 2, extent := 3 },
         { kind := .read, region := .synchronizedValues, index := 1, extent := 3 },
         { kind := .write, region := .synchronizedValues, index := 2, extent := 3 },
         { kind := .read, region := .synchronizedValues, index := 0, extent := 3 },
         { kind := .write, region := .synchronizedValues, index := 1, extent := 3 },
         { kind := .write, region := .synchronizedValues, index := 0, extent := 3 }] := by
  decide

/-- A rightmost insertion has a zero-length shift but still performs the
source's key-pivot write, value-pivot read, and value-pivot write in order. -/
private theorem binarysort_insert_end_no_shift_regression :
    (binarysortShiftInsertTraced? true binarysortEqualRegressionSlice 0 2 2
      { key := 2, value := some 21 }).result =
        some binarysortEqualRegressionSlice ∧
      (binarysortShiftInsertTraced? true binarysortEqualRegressionSlice 0 2 2
        { key := 2, value := some 21 }).trace.accesses =
        [{ kind := .write, region := .inputKeys, index := 2, extent := 3 },
         { kind := .read, region := .synchronizedValues, index := 2, extent := 3 },
         { kind := .write, region := .synchronizedValues, index := 2, extent := 3 }] := by
  decide

/-- With tagged equal keys, strict comparison is false and the search takes
the right branch past both older equal entries.  The full sort then shifts a
larger key and inserts the saved equal pivot after the older payloads. -/
private theorem binarysort_equal_pivot_stability_regression :
    (binarysortSearchTraced? 4 binarysortTaggedEqualRegressionState.key_compare
      binarysortTaggedEqualRegressionSlice 0 { key := 1, value := some 12 }
      0 3).result.map (fun result =>
        (result.position, result.fuelExhausted)) = some (2, false) ∧
      (binarysortTraced? binarysortTaggedEqualRegressionState
        binarysortTaggedEqualRegressionSlice 0 4 3).result.map
          (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
        some
          (false,
            [{ key := 1, value := some 10 },
             { key := 1, value := some 11 },
             { key := 1, value := some 12 },
             { key := 2, value := some 20 }]) := by
  decide

/-- A concrete assertion-domain rejection fails before any source access and
therefore has the empty trace. -/
private theorem binarysort_invalid_guard_regression :
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 0 0).result = none ∧
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 0 0).trace = AccessTrace.empty := by
  decide

/-- Concrete active calls reach both otherwise synthetic zero-fuel arms and
make exhaustion observable in both the returned status and trace. -/
private theorem binarysort_zero_fuel_regression :
    (binarysortSearchTraced? 0 binarysortRegressionState.key_compare
      binarysortEqualRegressionSlice 0 { key := 2, value := some 21 }
      0 1).result.map (·.fuelExhausted) = some true ∧
      (binarysortSearchTraced? 0 binarysortRegressionState.key_compare
        binarysortEqualRegressionSlice 0 { key := 2, value := some 21 }
        0 1).trace.fuelExhausted = true ∧
      (binarysortLoopTraced? 0 binarysortRegressionState
        binarysortEqualRegressionSlice 0 1 0).result.map
          (·.fuelExhausted) = some true ∧
      (binarysortLoopTraced? 0 binarysortRegressionState
        binarysortEqualRegressionSlice 0 1 0).trace.fuelExhausted = true := by
  decide

end CPythonListsort

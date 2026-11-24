/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.CountRunSafety

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Branch and failure anti-vacuity regressions -/

private def countRunRegressionState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := slice.entries.size
    basekeys := 0
    data := slice
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def countRunSingletonSlice : SortSlice Nat Nat :=
  { entries := #[{ key := 7, value := none }] }

private def countRunAscendingSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := none }, { key := 2, value := none },
        { key := 3, value := none }, { key := 4, value := none }] }

private def countRunDescendingSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 4, value := none }, { key := 3, value := none },
        { key := 2, value := none }, { key := 1, value := none }] }

private def countRunGateSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := none }, { key := 3, value := none },
        { key := 2, value := none }] }

private def countRunTaggedEqualSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := some 30 }, { key := 2, value := some 20 },
        { key := 2, value := some 21 }, { key := 1, value := some 10 }] }

private def countRunValuesRegressionState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { countRunRegressionState slice with
    a := { cells := #[], backing := .inline, hasValues := true } }

private def countRunExtensionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := none }, { key := 2, value := none },
        { key := 1, value := none }, { key := 3, value := none },
        { key := 4, value := none }, { key := 5, value := none },
        { key := 0, value := none }] }

private def countRunConstantTrueState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { countRunRegressionState slice with key_compare := fun _ _ => true }

/-- A singleton reaches the no-probe completion arm with length one. -/
private theorem countRunTraced_singleton_regression :
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 1).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some (1, false, countRunSingletonSlice.entries.toList) ∧
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 1).trace = AccessTrace.empty := by
  decide

/-- A full ascending run performs exactly the adjacent scan probes and does
not reread the endpoints in the post-scan direction check. -/
private theorem countRunTraced_full_ascending_no_reread_regression :
    (countRunTraced? (countRunRegressionState countRunAscendingSlice)
      countRunAscendingSlice 0 4).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some (4, false, countRunAscendingSlice.entries.toList) ∧
    (countRunTraced? (countRunRegressionState countRunAscendingSlice)
      countRunAscendingSlice 0 4).trace.accesses.map
        (fun event => (event.kind, event.region, event.index)) =
      [(.read, .inputKeys, 0), (.read, .inputKeys, 1),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.read, .inputKeys, 2), (.read, .inputKeys, 3)] := by
  decide

/-- A strict descending run reaches completion, reverses the whole prefix,
and returns the ascending sequence without exhausting fuel. -/
private theorem countRunTraced_descending_regression :
    (countRunTraced? (countRunRegressionState countRunDescendingSlice)
      countRunDescendingSlice 0 4).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some
        (4, false,
          [{ key := 1, value := none }, { key := 2, value := none },
           { key := 3, value := none }, { key := 4, value := none }]) ∧
    (countRunTraced? (countRunRegressionState countRunDescendingSlice)
      countRunDescendingSlice 0 4).trace.fuelExhausted = false := by
  decide

/-- The post-scan first/last gate is reachable: `[1,3,2]` discovers length
two, rereads indices zero and one, takes the true endpoint branch, and performs
no write. -/
private theorem countRunTraced_first_last_gate_regression :
    (countRunTraced? (countRunRegressionState countRunGateSlice)
      countRunGateSlice 0 3).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some (2, false, countRunGateSlice.entries.toList) ∧
    (countRunTraced? (countRunRegressionState countRunGateSlice)
      countRunGateSlice 0 3).trace.accesses.map
        (fun event => (event.kind, event.region, event.index)) =
      [(.read, .inputKeys, 0), (.read, .inputKeys, 1),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.read, .inputKeys, 0), (.read, .inputKeys, 1)] := by
  decide

/-- A tagged equal block is reversed locally before the whole descending
prefix.  The exact trace pins the local keys phase, local synchronized-values
phase, whole keys phase, and whole synchronized-values phase in that order;
the final equal keys retain payload order `20,21`. -/
private theorem countRunTraced_tagged_equal_block_order_regression :
    (countRunTraced? (countRunValuesRegressionState countRunTaggedEqualSlice)
      countRunTaggedEqualSlice 0 4).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some
        (4, false,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 2, value := some 21 },
           { key := 3, value := some 30 }]) ∧
    (countRunTraced? (countRunValuesRegressionState countRunTaggedEqualSlice)
      countRunTaggedEqualSlice 0 4).trace.accesses.map
        (fun event => (event.kind, event.region, event.index)) =
      [(.read, .inputKeys, 0), (.read, .inputKeys, 1),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.read, .inputKeys, 2), (.read, .inputKeys, 3),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.write, .inputKeys, 1), (.write, .inputKeys, 2),
       (.read, .synchronizedValues, 1),
       (.read, .synchronizedValues, 2),
       (.write, .synchronizedValues, 1),
       (.write, .synchronizedValues, 2),
       (.read, .inputKeys, 0), (.read, .inputKeys, 3),
       (.write, .inputKeys, 0), (.write, .inputKeys, 3),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.write, .inputKeys, 1), (.write, .inputKeys, 2),
       (.read, .synchronizedValues, 0),
       (.read, .synchronizedValues, 3),
       (.write, .synchronizedValues, 0),
       (.write, .synchronizedValues, 3),
       (.read, .synchronizedValues, 1),
       (.read, .synchronizedValues, 2),
       (.write, .synchronizedValues, 1),
       (.write, .synchronizedValues, 2)] := by
  decide

/-- After reversing the descending prefix `3,2,1`, the final ascending scan
extends through `3,4,5` and stops before the trailing zero. -/
private theorem countRunTraced_descending_then_ascending_extension_regression :
    (countRunTraced? (countRunRegressionState countRunExtensionSlice)
      countRunExtensionSlice 0 7).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some
        (6, false,
          [{ key := 1, value := none }, { key := 2, value := none },
           { key := 3, value := none }, { key := 3, value := none },
           { key := 4, value := none }, { key := 5, value := none },
           { key := 0, value := none }]) := by
  decide

/-- With a deliberately inconsistent constant-true comparator, the first
`next < previous` answer wins: the descending scan advances through the third
entry and returns length three.  This is an observable control-flow witness,
not a claim that comparator calls appear in `AccessTrace`. -/
private theorem countRunTraced_constant_true_priority_regression :
    (countRunTraced? (countRunConstantTrueState countRunGateSlice)
      countRunGateSlice 0 3).result.map
        (fun result => (result.length, result.fuelExhausted)) =
      some (3, false) ∧
    (countRunTraced? (countRunConstantTrueState countRunGateSlice)
      countRunGateSlice 0 3).trace.accesses.map
        (fun event => event.index) = [0, 1, 1, 2, 0, 2, 0, 2] := by
  decide

/-- The active zero-fuel ascending arm exposes exhaustion in both the returned
helper result and trace. -/
private theorem ascendingScanTraced_zero_fuel_active_regression :
    (ascendingScanTraced? 0 (fun (left right : Nat) => decide (left < right))
      countRunAscendingSlice 0 4 1).result.map
        (fun result => result.fuelExhausted) = some true ∧
    (ascendingScanTraced? 0 (fun (left right : Nat) => decide (left < right))
      countRunAscendingSlice 0 4 1).trace.fuelExhausted = true := by
  decide

/-- The analogous active zero-fuel descending arm is independently
observable. -/
private theorem descendingScanTraced_zero_fuel_active_regression :
    (descendingScanTraced? 0 false
      (fun (left right : Nat) => decide (left < right))
      countRunDescendingSlice 0 4 2 0).result.map
        (fun result => result.fuelExhausted) = some true ∧
    (descendingScanTraced? 0 false
      (fun (left right : Nat) => decide (left < right))
      countRunDescendingSlice 0 4 2 0).trace.fuelExhausted = true := by
  decide

/-- The public assertion guard's zero-length failure arm is concrete and has
no fabricated accesses. -/
private theorem countRunTraced_zero_remaining_failure_regression :
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 0).result = none ∧
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 0).trace = AccessTrace.empty := by
  decide

/-- An overstated remaining length preserves the successful first probe and
the rejected one-past probe, making the access-failure path non-vacuous. -/
private theorem countRunTraced_oob_failure_regression :
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 2).result = none ∧
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 2).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 0, extent := 1 },
       { kind := .read, region := .inputKeys, index := 1, extent := 1 }] ∧
    ¬(countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 2).trace.allAccessesInBounds := by
  decide

end CPythonListsort

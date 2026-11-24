/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.ListSortTrace

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

private def listSortZeroFuelRegressionSlice : SortSlice Nat PUnit :=
  { entries :=
      #[{ key := 2, value := none },
        { key := 1, value := none }] }

private def listSortZeroFuelRegressionState : MergeState Nat PUnit :=
  (initialMergeState (fun left right : Nat => decide (left < right)) false
    listSortZeroFuelRegressionSlice).1

/-- The active zero-fuel scan arm is observably reachable: it returns the
modeled `-1`/fuel-exhausted result, marks the trace, and still erases to the
reviewed raw evaluator. -/
private theorem listSortScanTraced_zero_fuel_active_regression :
    (listSortScanTraced? 0 listSortZeroFuelRegressionState 0 2 false 2).result.map
        (fun result => (result.returnCode, result.fuelExhausted)) =
      some (-1, true) ∧
    (listSortScanTraced? 0 listSortZeroFuelRegressionState 0 2 false 2).trace.fuelExhausted =
      true ∧
    (listSortScanTraced? 0 listSortZeroFuelRegressionState 0 2 false 2).erase =
      listSortScan? 0 listSortZeroFuelRegressionState 0 2 false 2 := by
  constructor
  · decide
  constructor
  · decide
  · rfl

/-! ## Formed-run event anti-vacuity -/

private def formedRunPolicyRegressionInput : SortSlice Nat Unit :=
  { entries :=
      #[{ key := 1, value := none },
        { key := 2, value := none },
        { key := 3, value := none }] }

/-- A complete source-admitted execution reaches the successful scan push and
exposes the rich formed-run observation on the real top-level trace.  The
strictly increasing input is one natural run, so its natural length, target,
physical length, and pre-consumption remainder are all three. -/
private theorem listSortImplTraced_formedRun_policy_regression :
    (listSortImplTraced? (fun left right : Nat => decide (left < right))
      false false formedRunPolicyRegressionInput).trace.policyEvents =
      [.formed
        { run := { base := 0, len := 3 }
          depthAfter := 1
          naturalLength := 3
          target := 3
          remainingBefore := 3 }] := by
  decide

private def formedRunExtensionRegressionInput : SortSlice Nat Unit :=
  { entries :=
      #[{ key := 3, value := none },
        { key := 1, value := none },
        { key := 2, value := none },
        { key := 4, value := none },
        { key := 5, value := none },
        { key := 6, value := none },
        { key := 7, value := none },
        { key := 8, value := none }] }

/-- The extended-short-run path keeps the discovered natural length distinct
from the adaptive target and the physical run length pushed after binarysort.
This regression prevents a future transcription from silently filling all
three fields with the post-extension length. -/
private theorem listSortImplTraced_extendedRun_policy_regression :
    (listSortImplTraced? (fun left right : Nat => decide (left < right))
      false false formedRunExtensionRegressionInput).trace.policyEvents =
      [.formed
        { run := { base := 0, len := 8 }
          depthAfter := 1
          naturalLength := 2
          target := 8
          remainingBefore := 8 }] := by
  decide

end CPythonListsort

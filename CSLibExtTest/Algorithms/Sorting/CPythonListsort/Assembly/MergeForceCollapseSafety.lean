/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.MergeForceCollapseSafety

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Branch and failure anti-vacuity regressions -/

private def forceCollapseTwoRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 0
    data := { entries := #[] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 1, power := none }]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Concrete two-run regression: the only allowed index is zero and selecting
it performs no neighboring-length read. -/
private theorem forceCollapseIndexTraced_two_run_regression :
    forceCollapseIndexTraced? forceCollapseTwoRegressionState =
      { result := some 0, trace := AccessTrace.empty } := by
  decide

private def forceCollapseEmptyRegressionState : MergeState Nat Nat :=
  { forceCollapseTwoRegressionState with pending := #[] }

/-- The selector's out-of-loop failure arm is observable on a concrete empty
stack and agrees with `forceCollapseIndex? = none`; the collapse loop itself
short-circuits before calling this arm. -/
private theorem forceCollapseIndexTraced_empty_failure_regression :
    forceCollapseIndexTraced? forceCollapseEmptyRegressionState =
      { result := none, trace := AccessTrace.empty } ∧
    forceCollapseIndex? forceCollapseEmptyRegressionState = none := by
  decide

private def forceCollapseLowerRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data := { entries := #[] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 2, power := none },
        { base := 3, len := 3, power := none }]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def forceCollapseTieRegressionState : MergeState Nat Nat :=
  { forceCollapseLowerRegressionState with
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 2, power := none },
        { base := 3, len := 1, power := none }] }

/-- Concrete strict signed-comparison regression: the lower pair is selected
after the two neighboring records are read in the sequential Lean model's
order. -/
private theorem forceCollapseIndexTraced_lower_branch_regression :
    forceCollapseIndexTraced? forceCollapseLowerRegressionState =
      { result := some 0
        trace :=
          { accesses :=
              [{ kind := .read, region := .pendingRuns, index := 0, extent := 3 },
               { kind := .read, region := .pendingRuns, index := 2, extent := 3 }]
            pushDepths := []
            fuelExhausted := false } } := by
  decide

/-- Concrete equality regression: the strict comparison is false on a tie, so
the top pair is selected after the same ordered reads. -/
private theorem forceCollapseIndexTraced_tie_chooses_top_regression :
    forceCollapseIndexTraced? forceCollapseTieRegressionState =
      { result := some 1
        trace :=
          { accesses :=
              [{ kind := .read, region := .pendingRuns, index := 0, extent := 3 },
               { kind := .read, region := .pendingRuns, index := 2, extent := 3 }]
            pushDepths := []
            fuelExhausted := false } } := by
  decide

/-- The synthetic zero-fuel failure is observably reachable on a concrete
three-run state. -/
private theorem mergeForceCollapseLoopTraced_zero_fuel_regression :
    (mergeForceCollapseLoopTraced? 0 forceCollapseTieRegressionState).result.map
        (fun result => (result.returnCode, result.fuelExhausted)) =
      some (-1, true) ∧
    (mergeForceCollapseLoopTraced? 0
      forceCollapseTieRegressionState).trace.fuelExhausted = true ∧
    (mergeForceCollapseLoopTraced? 0
      forceCollapseTieRegressionState).erase =
      mergeForceCollapseLoop? 0 forceCollapseTieRegressionState := by
  constructor
  · decide
  constructor
  · decide
  · exact erase_mergeForceCollapseLoopTraced_zero _

private def forceCollapseRejectedMergeState : MergeState Nat Nat :=
  { forceCollapseTieRegressionState with
    listlen := 0
    pending :=
      #[{ base := 0, len := 0, power := none },
        { base := 0, len := 0, power := none }] }

/-- Concrete delegated-failure regression: selection succeeds, `merge_at`
records both pending reads, and its nonpositive-run guard rejects the call.
The failure retains those events and does not masquerade as fuel exhaustion. -/
private theorem mergeForceCollapseLoopTraced_delegated_failure_regression :
    (mergeForceCollapseLoopTraced? 1
      forceCollapseRejectedMergeState).result = none ∧
    (mergeForceCollapseLoopTraced? 1
      forceCollapseRejectedMergeState).trace.accesses =
      [{ kind := .read, region := .pendingRuns, index := 0, extent := 2 },
       { kind := .read, region := .pendingRuns, index := 1, extent := 2 }] ∧
    (mergeForceCollapseLoopTraced? 1
      forceCollapseRejectedMergeState).trace.fuelExhausted = false := by
  decide

end CPythonListsort

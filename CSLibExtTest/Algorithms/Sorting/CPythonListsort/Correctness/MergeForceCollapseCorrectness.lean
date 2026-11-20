/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.MergeForceCollapseCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.RuntimeAssert

namespace CPythonListsort

private def forceCollapseCorrectnessRegressionLt : BoolComparator Nat :=
  fun _ _ => false

private def forceCollapseCorrectnessRegressionEntry
    (origin payload : Nat) : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 7, origin := origin }, value := some payload }

private def forceCollapseCorrectnessRegressionState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[forceCollapseCorrectnessRegressionEntry 0 10,
            forceCollapseCorrectnessRegressionEntry 1 20,
            forceCollapseCorrectnessRegressionEntry 2 30] }
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 1 },
        { base := 1, len := 1, power := some 2 },
        { base := 2, len := 1, power := none }]
    key_compare := occurrenceComparator forceCollapseCorrectnessRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private structure ForceCollapseCorrectnessRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  pending : List (Nat × Nat)
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

private def forceCollapseCorrectnessRegressionView
    (result : MergeForceCollapseResult (Occurrence Nat) Nat) :
    ForceCollapseCorrectnessRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    pending := result.state.pending.toList.map (fun run =>
      (run.base, run.len.toNat))
    entries := result.state.data.entries.toList.map (fun entry =>
      (entry.key.value, entry.key.origin, entry.value)) }

private def forceCollapseCorrectnessRegressionExpected :
    ForceCollapseCorrectnessRegressionView :=
  { returnCode := 0
    fuelExhausted := false
    pending := [(0, 3)]
    entries := [(7, 0, some 10), (7, 1, some 20), (7, 2, some 30)] }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Native evaluation unfolds two complete merge continuations and their loops.
/-- A concrete three-run execution of the real evaluator returns one
three-element run.  All underlying keys compare equal, yet absolute-origin
order and the paired payloads survive the complete collapse. -/
def mergeForceCollapse_threeRun_equalKey_payload_regression : IO Unit :=
  CPythonListsortTest.assertTrue "mergeForceCollapse_threeRun_equalKey_payload_regression" (decide (
    (mergeForceCollapse? forceCollapseCorrectnessRegressionState).map
        forceCollapseCorrectnessRegressionView =
      some forceCollapseCorrectnessRegressionExpected))

#eval mergeForceCollapse_threeRun_equalKey_payload_regression

end CPythonListsort

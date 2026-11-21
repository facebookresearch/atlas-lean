/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.ScanStepCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.RuntimeAssert

namespace CPythonListsort

/-! ## Concrete branch witnesses -/

private def scanStepRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def scanStepRegressionEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := value, origin := origin }, value := some payload }

private def scanStepExtensionSlice : SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[scanStepRegressionEntry 99 0 10,
        scanStepRegressionEntry 3 1 11,
        scanStepRegressionEntry 1 2 12,
        scanStepRegressionEntry 2 3 13,
        scanStepRegressionEntry 0 4 14,
        scanStepRegressionEntry 77 5 15] }

private def scanStepExtensionState : MergeState (Occurrence Nat) Nat :=
  (initialMergeState (occurrenceComparator scanStepRegressionLt) true
    scanStepExtensionSlice).1

private structure ScanStepExtensionRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  pending : List (Nat × Nat)
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

private def scanStepExtensionRegressionView
    (result : ListSortImplResult (Occurrence Nat) Nat) :
    ScanStepExtensionRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    pending := result.state.pending.toList.map (fun run =>
      (run.base, run.len.toNat))
    entries := result.state.data.entries.toList.map (fun entry =>
      (entry.key.value, entry.key.origin, entry.value)) }

private def scanStepExtensionRegressionExpected :
    ScanStepExtensionRegressionView :=
  { returnCode := 0
    fuelExhausted := false
    pending := [(1, 4)]
    entries :=
      [(99, 0, some 10), (0, 4, some 14), (1, 2, some 12),
       (2, 3, some 13), (3, 1, some 11), (77, 5, some 15)] }

set_option maxRecDepth 100000 in
/-- Concrete extension witness through the real scan evaluator.  `count_run`
finds only the descending pair, while the scan sorts the full forced range of
four; the keyed payloads travel with their occurrences and both outside
sentinels remain byte-for-byte observable. -/
theorem listSortScan_short_run_extension_regression :
    (countRun? scanStepExtensionState scanStepExtensionState.data 1 4).map
        (fun counted => counted.length) = some 2 ∧
      (listSortScan? 1 scanStepExtensionState 1 4 false 6).map
        scanStepExtensionRegressionView =
        some scanStepExtensionRegressionExpected := by
  constructor <;> decide

private def scanStepNoExtensionSlice : SortSlice (Occurrence Nat) PUnit.{1} :=
  { entries := (Array.range 64).map fun index =>
      ({ key := { value := index, origin := index }, value := none } :
        SortSliceEntry (Occurrence Nat) PUnit.{1}) }

private def scanStepNoExtensionState : MergeState (Occurrence Nat) PUnit.{1} :=
  let initialized :=
    (initialMergeState (occurrenceComparator scanStepRegressionLt) false
      scanStepNoExtensionSlice).1
  { initialized with
    pending := #[{ base := 0, len := BitVec.ofNat 64 24, power := none }] }

set_option maxRecDepth 100000 in
/-- Concrete no-extension witness through the real scan evaluator.  The
natural run has length `40`, strictly above the adaptive target `32`; it is
therefore consumed at its own length, pushed after the existing 24-element
prefix, and the final collapse recovers one unchanged 64-element run. -/
def listSortScan_long_run_no_extension_regression : IO Unit :=
  CPythonListsortTest.assertTrue "listSortScan_long_run_no_extension_regression" (decide (
    (minrunNext scanStepNoExtensionState.minrunState).result.toNat = 32 ∧
      (countRun? scanStepNoExtensionState scanStepNoExtensionState.data 24 40).map
        (fun counted => counted.length) = some 40 ∧
      (listSortScanTraced? 1 scanStepNoExtensionState 24 40 false 64).trace.pushDepths =
        [2] ∧
      (listSortScan? 1 scanStepNoExtensionState 24 40 false 64).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList.map (fun run =>
              (run.base, run.len.toNat)),
            decide (result.state.data = scanStepNoExtensionSlice))) =
        some (0, false, [(0, 64)], true)))

#eval listSortScan_long_run_no_extension_regression

private def scanStepPolicyMergeEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit.{1} :=
  { key := { value := value, origin := origin }, value := none }

private def scanStepPolicyMergeState : MergeState (Occurrence Nat) PUnit.{1} :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[scanStepPolicyMergeEntry 2 0,
            scanStepPolicyMergeEntry 1 1,
            scanStepPolicyMergeEntry 3 2] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 3 },
        { base := 1, len := 1, power := none }]
    key_compare := occurrenceComparator scanStepRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option maxRecDepth 100000 in
/-- Concrete policy-merge-then-push witness through the real traced scan.  A
direct push from depth two would record depth three; the observed depth two
therefore pins the preceding strict-power merge before the unconditional
push.  Final collapse then produces the sorted three-element run. -/
def listSortScan_policy_merge_then_push_regression : IO Unit :=
  CPythonListsortTest.assertTrue "listSortScan_policy_merge_then_push_regression" (decide (
    (countRun? scanStepPolicyMergeState scanStepPolicyMergeState.data 2 1).map
        (fun counted => counted.length) = some 1 ∧
      (listSortScanTraced? 1 scanStepPolicyMergeState 2 1 false 3).trace.pushDepths =
        [2] ∧
      (listSortScan? 1 scanStepPolicyMergeState 2 1 false 3).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList.map (fun run =>
              (run.base, run.len.toNat)),
            result.state.data.entries.toList.map (fun entry =>
              (entry.key.value, entry.key.origin)))) =
        some (0, false, [(0, 3)], [(1, 1), (2, 0), (3, 2)])))

#eval listSortScan_policy_merge_then_push_regression

end CPythonListsort

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.MergeAtSafety

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Logical-event anti-vacuity regression -/

private def mergeAtPolicyEarlyTrimLeft : PendingRun :=
  { base := 0, len := 1, power := some 4 }

private def mergeAtPolicyEarlyTrimRight : PendingRun :=
  { base := 1, len := 1, power := some 7 }

private def mergeAtPolicyEarlyTrimTail : PendingRun :=
  { base := 2, len := 1, power := none }

private def mergeAtPolicyEarlyTrimState : MergeState Nat Nat :=
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
      #[mergeAtPolicyEarlyTrimLeft,
        mergeAtPolicyEarlyTrimRight,
        mergeAtPolicyEarlyTrimTail]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeAtPolicyEarlyTrimCall : MergeState Nat Nat :=
  { mergeAtPolicyEarlyTrimState with pending :=
      #[{ mergeAtPolicyEarlyTrimLeft with len := 2 }, mergeAtPolicyEarlyTrimTail] }

private def mergeAtFinishedSuccessShape
    (prepared : MergeAtPreparation Nat Nat) : Option (Int × Bool) :=
  match prepared with
  | .finished result => some (result.returnCode, result.fuelExhausted)
  | .mergeLo _ | .mergeHi _ => none

/-- This concrete input reaches the `na = 0` early-trim exit: the first gallop
returns the whole left-run length, preparation finishes successfully, and the
complete `merge_at` emits its logical full-run merge even though no directional
merge-memory call occurs.  The proof uses kernel reduction, not native evaluation. -/
theorem mergeAtTraced_earlyTrim_recordsLogicalMerge :
    (gallopRightTraced? mergeAtPolicyEarlyTrimCall
        (.main mergeAtPolicyEarlyTrimCall.data 0) 2 1 0).result =
      some { index := 1, fuelExhausted := false } ∧
    (prepareMergeAtTraced? mergeAtPolicyEarlyTrimState 0).result.bind
        mergeAtFinishedSuccessShape = some (0, false) ∧
    (mergeAtTraced? mergeAtPolicyEarlyTrimState 0).trace.policyEvents =
      [.merge
        { index := 0
          left := { base := 0, len := 1 }
          right := { base := 1, len := 1 } }] ∧
    (mergeAtTraced? mergeAtPolicyEarlyTrimState 0).trace.memoryEvents = [] := by
  decide

end CPythonListsort

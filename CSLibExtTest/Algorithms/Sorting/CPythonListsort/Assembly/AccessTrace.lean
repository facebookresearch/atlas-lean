/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.AccessTrace

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Executable regressions -/

private def accessTraceRegressionRun : PendingRun :=
  { base := 0, len := 1, power := none }

/-- A concrete pending array at the C capacity, used only to demonstrate the
trace semantics without requiring an otherwise irrelevant `MergeState`. -/
private def accessTraceCapacityPending : Array PendingRun :=
  Array.replicate MAX_MERGE_PENDING accessTraceRegressionRun

/-- The same total push performed by `pushPendingRunTraced`, projected to the
pending array for a closed executable capacity regression. -/
private def accessTraceForcedPush : TraceResult (Array PendingRun) :=
  let pushed := accessTraceCapacityPending.push accessTraceRegressionRun
  { result := some pushed
    trace := AccessTrace.singletonPushDepth pushed.size }

/-- At depth 64 the modeled push physically succeeds and records 65.  The
trace has no capacity-failure or assertion-event channel that could make this
fact true vacuously. -/
theorem forcedPushAtCapacity_records65 :
    accessTraceForcedPush.result.map Array.size = some 65 ∧
      accessTraceForcedPush.trace.pushDepths = [65] ∧
      accessTraceForcedPush.trace.stackDepthMax = 65 := by
  decide

private def releasedTempStorage : TempStorage Nat Nat :=
  { cells := #[]
    backing := .released
    hasValues := true }

private def rejectedReleasedTempRead : TraceResult (SortSliceEntry Nat Nat) :=
  TraceResult.tempPayloadRead? releasedTempStorage 0

/-- A rejected temporary access is still recorded, so both its bad upper bound
and its released backing remain visible to their separate predicates. -/
theorem rejectedReleasedTempRead_is_observable :
    rejectedReleasedTempRead.result = none ∧
      rejectedReleasedTempRead.trace.accesses =
        [{ kind := .read, region := .tempPayload .released,
           index := 0, extent := 0 }] ∧
      ¬rejectedReleasedTempRead.trace.allAccessesInBounds ∧
      ¬rejectedReleasedTempRead.trace.tempPayloadAccessesLive := by
  decide

private def uninitializedTempStorage : TempStorage Nat Nat :=
  { cells := #[none]
    backing := .inline
    hasValues := true }

private def rejectedUninitializedTempRead :
    TraceResult (SortSliceEntry Nat Nat) :=
  TraceResult.tempPayloadRead? uninitializedTempStorage 0

/-- Rejection because a live in-bounds cell is uninitialized does not erase
the attempt or falsely fail either the bounds or backing-liveness predicate. -/
theorem rejectedUninitializedTempRead_is_observable :
    rejectedUninitializedTempRead.result = none ∧
      rejectedUninitializedTempRead.trace.accesses =
        [{ kind := .read, region := .tempPayload .inline,
           index := 0, extent := 1 }] ∧
      rejectedUninitializedTempRead.trace.allAccessesInBounds ∧
      rejectedUninitializedTempRead.trace.tempPayloadAccessesLive := by
  decide

private def orderedAccessSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 4, value := some 40 },
        { key := 9, value := some 90 }] }

private def orderedAccessRegression : TraceResult (SortSlice Nat Nat) :=
  (TraceResult.sortSliceKeysRead? orderedAccessSlice 1).bind fun entry =>
    TraceResult.sortSliceValuesWrite? orderedAccessSlice 0 entry

/-- Local evaluator composition keeps access attempts in execution order. -/
theorem localTraceComposition_preserves_order :
    orderedAccessRegression.trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 1, extent := 2 },
       { kind := .write, region := .synchronizedValues, index := 0, extent := 2 }] ∧
      orderedAccessRegression.trace.allAccessesInBounds ∧
      orderedAccessRegression.trace.tempPayloadAccessesLive := by
  decide

end CPythonListsort

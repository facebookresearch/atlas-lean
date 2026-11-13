/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.BinarysortSafety
import Code.Assembly.CountRunSafety
import Code.Assembly.FoundNewRunSafety
import Code.Assembly.ListSortInputMode
import Code.Assembly.ListSortSupport
import Code.Assembly.MergeForceCollapseSafety
import Code.Assembly.ReverseSliceSafety

/-!
# Traced top-level `list_sort_impl`

This module assembles the genuine top-level access trace from the already
instrumented helper evaluators.  In particular, the scan uses the traced
`count_run`, `binarysort`, `found_new_run`, pending push, and final-collapse
operations directly; it never computes an untraced result and attaches a
synthetic trace afterward.

The two reverse-sort sites intentionally have different physical traces.  The
initial site models CPython's key reversal followed by the saved-list/value
reversal in keyed mode.  The final site models only the reversal of
`saved_ob_item`: synchronized values in keyed mode and keys in unkeyed mode.
Both physical phases erase to the same paired-snapshot semantic reversal.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Initial reverse-sort instrumentation.  Unlike final cleanup, the keyed
case executes both physical phases through the reviewed paired-snapshot
wrapper. -/
def listSortInitialReverseTraced? (state : MergeState κ ν) (inputSize : Nat) :
    TraceResult (ReverseSliceResult κ ν) :=
  sortsliceReverseTraced? state.a.hasValues state.data 0 inputSize

@[simp]
theorem listSortInitialReverseTraced_unkeyed (state : MergeState κ ν)
    (inputSize : Nat) (hMode : state.a.hasValues = false) :
    listSortInitialReverseTraced? state inputSize =
      sortsliceReverseTraced? false state.data 0 inputSize := by
  simp [listSortInitialReverseTraced?, hMode]

@[simp]
theorem listSortInitialReverseTraced_keyed (state : MergeState κ ν)
    (inputSize : Nat) (hMode : state.a.hasValues = true) :
    listSortInitialReverseTraced? state inputSize =
      sortsliceReverseTraced? true state.data 0 inputSize := by
  simp [listSortInitialReverseTraced?, hMode]

/-- In keyed mode, the initial reverse executes the complete keys phase before
the complete synchronized-values phase; both phases start from the same paired
snapshot, matching the representation abstraction used by the model. -/
theorem listSortInitialReverseTraced_trace_keyed (state : MergeState κ ν)
    (inputSize : Nat) (hMode : state.a.hasValues = true)
    (keyResult : ReverseSliceResult κ ν)
    (hKey :
      (reverseSlicePhaseTraced? .keys state.data 0
        (Int.ofNat inputSize)).result = some keyResult) :
    (listSortInitialReverseTraced? state inputSize).trace =
      (reverseSlicePhaseTraced? .keys state.data 0
        (Int.ofNat inputSize)).trace.compose
      (reverseSlicePhaseTraced? .values state.data 0
        (Int.ofNat inputSize)).trace := by
  rw [listSortInitialReverseTraced?, hMode]
  simpa using
    sortsliceReverseTraced_values_trace_order state.data 0 inputSize keyResult
      (by simpa using hKey)

/-- In unkeyed mode, the initial reverse has exactly one keys phase. -/
theorem listSortInitialReverseTraced_trace_unkeyed (state : MergeState κ ν)
    (inputSize : Nat) (hMode : state.a.hasValues = false) :
    (listSortInitialReverseTraced? state inputSize).trace =
      (reverseSlicePhaseTraced? .keys state.data 0
        (Int.ofNat inputSize)).trace := by
  rw [listSortInitialReverseTraced?, hMode]
  simpa using
    sortsliceReverseTraced_no_values_trace_order state.data 0 inputSize

/-- The raw merge-memory boundary emitted by the top-level cleanup.

The two snapshots are computed from the actual state passed to
`mergeFreemem`, rather than reconstructed from its released result. -/
def listSortCleanupMemoryEvent (before : MergeState κ ν) :
    MergeMemoryEvent :=
  .cleanup (MergeMemorySnapshot.ofState before)
    (MergeMemorySnapshot.ofState (mergeFreemem before))

/-- Traced common `succeed`/`fail` cleanup.  The final reversal is one physical
`reverse_slice` call, selected from the retained storage-mode bit.  Every
successful cleanup appends one raw merge-memory boundary after the physical
reverse trace and before returning the post-cleanup state. -/
def finishListSortTraced? (state : MergeState κ ν) (reverse : Bool)
    (inputSize : Nat) (returnCode : Int) (fuelExhausted : Bool) :
    TraceResult (ListSortImplResult κ ν) :=
  if reverse && decide (1 < inputSize) then
    (reverseSlicePhaseTraced? (finalReversePhase state.a.hasValues)
      state.data 0 (Int.ofNat inputSize)).bind fun reversed =>
        let before : MergeState κ ν := { state with data := reversed.slice }
        (TraceResult.pure
          { state := mergeFreemem before
            returnCode := returnCode
            fuelExhausted := fuelExhausted || reversed.fuelExhausted }).appendMemoryEvent
          (listSortCleanupMemoryEvent before)
  else
    (TraceResult.pure
      { state := mergeFreemem state
        returnCode := returnCode
        fuelExhausted := fuelExhausted }).appendMemoryEvent
      (listSortCleanupMemoryEvent state)

/-- Failure adapter for a completed traced `found_new_run` call.  The helper's
trace is composed by the caller; this adapter contributes only the real final
reverse/cleanup trace. -/
def failFromFoundNewRunTraced? (result : FoundNewRunResult κ ν)
    (reverse : Bool) (inputSize : Nat) :
    TraceResult (ListSortImplResult κ ν) :=
  finishListSortTraced? result.state reverse inputSize result.returnCode
    result.fuelExhausted

/-- Failure adapter for a completed traced `merge_force_collapse` call. -/
def failFromCollapseTraced? (result : MergeForceCollapseResult κ ν)
    (reverse : Bool) (inputSize : Nat) :
    TraceResult (ListSortImplResult κ ν) :=
  finishListSortTraced? result.state reverse inputSize result.returnCode
    result.fuelExhausted

/-- In keyed mode, an active final reverse records the complete
synchronized-values trace followed by exactly the cleanup boundary formed
from the post-reversal state actually passed to `mergeFreemem`.  It is the C
`reverse_slice(saved_ob_item, ...)` call, not another two-phase
`sortslice_reverse`. -/
theorem finishListSortTraced_trace_keyed (state : MergeState κ ν)
    (inputSize : Nat) (returnCode : Int) (fuelExhausted : Bool)
    (hMode : state.a.hasValues = true) (hSize : 1 < inputSize)
    (reversed : ReverseSliceResult κ ν)
    (hReversed :
      (reverseSlicePhaseTraced? .values state.data 0
        (Int.ofNat inputSize)).result = some reversed) :
    (finishListSortTraced? state true inputSize returnCode fuelExhausted).trace =
      (reverseSlicePhaseTraced? .values state.data 0
        (Int.ofNat inputSize)).trace.compose
      (AccessTrace.singletonMemoryEvent
        (listSortCleanupMemoryEvent
          { state with data := reversed.slice })) := by
  unfold finishListSortTraced?
  rw [if_pos (by simp [hSize])]
  simp only [hMode, finalReversePhase, if_true]
  rw [TraceResult.trace_bind, hReversed]
  rfl

/-- In unkeyed mode, `saved_ob_item` is the key array, so an active final
reverse records one keys phase followed by the exact cleanup boundary. -/
theorem finishListSortTraced_trace_unkeyed (state : MergeState κ ν)
    (inputSize : Nat) (returnCode : Int) (fuelExhausted : Bool)
    (hMode : state.a.hasValues = false) (hSize : 1 < inputSize)
    (reversed : ReverseSliceResult κ ν)
    (hReversed :
      (reverseSlicePhaseTraced? .keys state.data 0
        (Int.ofNat inputSize)).result = some reversed) :
    (finishListSortTraced? state true inputSize returnCode fuelExhausted).trace =
      (reverseSlicePhaseTraced? .keys state.data 0
        (Int.ofNat inputSize)).trace.compose
      (AccessTrace.singletonMemoryEvent
        (listSortCleanupMemoryEvent
          { state with data := reversed.slice })) := by
  unfold finishListSortTraced?
  rw [if_pos (by simp [hSize])]
  simp only [hMode, finalReversePhase, Bool.false_eq_true, if_false]
  rw [TraceResult.trace_bind, hReversed]
  rfl

/-- On every inactive-final-reverse path, the cleanup trace is exactly one
boundary formed from `state` and its actual `mergeFreemem` successor. -/
theorem finishListSortTraced_cleanup_event_inactive_exact
    (state : MergeState κ ν) (reverse : Bool) (inputSize : Nat)
    (returnCode : Int) (fuelExhausted : Bool)
    (hInactive : (reverse && decide (1 < inputSize)) = false) :
    (finishListSortTraced? state reverse inputSize returnCode
      fuelExhausted).trace.memoryEvents =
      [listSortCleanupMemoryEvent state] := by
  unfold finishListSortTraced?
  rw [if_neg (by simpa using hInactive)]
  rfl

/-- On an active final-reverse path that returns `reversed`, the exact cleanup
boundary is appended after the reversal observations and is computed from the
updated state passed to `mergeFreemem`. -/
theorem finishListSortTraced_cleanup_event_active_exact
    (state : MergeState κ ν) (reverse : Bool) (inputSize : Nat)
    (returnCode : Int) (fuelExhausted : Bool)
    (hActive : (reverse && decide (1 < inputSize)) = true)
    (reversed : ReverseSliceResult κ ν)
    (hReversed :
      (reverseSlicePhaseTraced? (finalReversePhase state.a.hasValues)
        state.data 0 (Int.ofNat inputSize)).result = some reversed) :
    (finishListSortTraced? state reverse inputSize returnCode
      fuelExhausted).trace.memoryEvents =
      (reverseSlicePhaseTraced? (finalReversePhase state.a.hasValues)
        state.data 0 (Int.ofNat inputSize)).trace.memoryEvents ++
      [listSortCleanupMemoryEvent { state with data := reversed.slice }] := by
  unfold finishListSortTraced?
  rw [if_pos (by simpa using hActive), TraceResult.trace_bind, hReversed]
  rfl

/-! ## Top-level helper policy-event freedom -/

/-- Initial reverse instrumentation contributes no formed-run or logical
merge event, in either keyed or unkeyed mode. -/
theorem listSortInitialReverseTraced_policyEvents_eq_nil
    (state : MergeState κ ν) (inputSize : Nat) :
    (listSortInitialReverseTraced? state inputSize).trace.policyEvents = [] := by
  exact sortsliceReverseTraced_policyEvents_eq_nil _ _ _ _

/-- Final physical reversal and cleanup contribute no logical policy event.
The cleanup boundary remains visible only in the merge-memory channel. -/
theorem finishListSortTraced_policyEvents_eq_nil
    (state : MergeState κ ν) (reverse : Bool) (inputSize : Nat)
    (returnCode : Int) (fuelExhausted : Bool) :
    (finishListSortTraced? state reverse inputSize returnCode
      fuelExhausted).trace.policyEvents = [] := by
  unfold finishListSortTraced?
  by_cases hactive : (reverse && decide (1 < inputSize)) = true
  · rw [if_pos hactive]
    apply TraceResult.policyEvents_bind_eq_nil
    · exact reverseSlicePhaseTraced_policyEvents_eq_nil _ _ _ _
    · intro reversed
      rfl
  · rw [if_neg hactive]
    rfl

/-- The `found_new_run` failure adapter contributes no logical policy event. -/
theorem failFromFoundNewRunTraced_policyEvents_eq_nil
    (result : FoundNewRunResult κ ν) (reverse : Bool) (inputSize : Nat) :
    (failFromFoundNewRunTraced? result reverse
      inputSize).trace.policyEvents = [] := by
  exact finishListSortTraced_policyEvents_eq_nil _ _ _ _ _

/-- The final-collapse failure adapter contributes no logical policy event. -/
theorem failFromCollapseTraced_policyEvents_eq_nil
    (result : MergeForceCollapseResult κ ν) (reverse : Bool)
    (inputSize : Nat) :
    (failFromCollapseTraced? result reverse inputSize).trace.policyEvents = [] := by
  exact finishListSortTraced_policyEvents_eq_nil _ _ _ _ _

/-! The following small continuations factor the scan without changing its
control flow.  Each traced helper has an untraced twin used only to make the
structural erasure argument local. -/

/-- Untraced semantic twin of the post-extension continuation.  It is exported
so the top-level safety induction can reason branchwise without unfolding or
duplicating the evaluator. -/
def listSortAfterExtension? (next : MergeState κ ν → Nat → Nat →
    Option (ListSortImplResult κ ν)) (lo remaining : Nat) (reverse : Bool)
    (inputSize : Nat) (extension : MergeState κ ν × Nat × Bool) :
    Option (ListSortImplResult κ ν) :=
  let state := extension.1
  let runLength := extension.2.1
  let extensionFuel := extension.2.2
  if extensionFuel then
    finishListSort? state reverse inputSize (-1) true
  else if runLength = 0 ∨ remaining < runLength then
    none
  else
    match foundNewRun? state runLength with
    | none => none
    | some found =>
        if found.returnCode = 0 ∧ !found.fuelExhausted then
          let newRun : PendingRun :=
            { base := lo
              len := BitVec.ofNat 64 runLength
              power := none }
          next (pushPendingRun found.state newRun) (lo + runLength)
            (remaining - runLength)
        else
          failFromFoundNewRun? found reverse inputSize

/-- Traced post-extension continuation, including `found_new_run`, the actual
unconditional push, and the recursive scan call. -/
def listSortAfterExtensionTraced?
    (next : MergeState κ ν → Nat → Nat →
      TraceResult (ListSortImplResult κ ν))
    (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
    (naturalLength target : Nat)
    (extension : MergeState κ ν × Nat × Bool) :
    TraceResult (ListSortImplResult κ ν) :=
  let state := extension.1
  let runLength := extension.2.1
  let extensionFuel := extension.2.2
  if extensionFuel then
    finishListSortTraced? state reverse inputSize (-1) true
  else if runLength = 0 ∨ remaining < runLength then
    TraceResult.failure
  else
    (foundNewRunTraced? state runLength).bind fun found =>
      if found.returnCode = 0 ∧ !found.fuelExhausted then
        let newRun : PendingRun :=
          { base := lo
            len := BitVec.ofNat 64 runLength
            power := none }
        (pushFormedRunTraced found.state newRun naturalLength target
          remaining).bind fun state =>
          next state (lo + runLength) (remaining - runLength)
      else
        failFromFoundNewRunTraced? found reverse inputSize

/-- On the successful post-extension path, the actual scan trace places the
formed-run observation after every policy event emitted by `found_new_run` and
before every event emitted by the recursive continuation.  The event retains
the natural-run length and adaptive-minrun target separately from the physical
run length that was pushed. -/
theorem listSortAfterExtensionTraced_policyEvents_of_success
    (next : MergeState κ ν → Nat → Nat →
      TraceResult (ListSortImplResult κ ν))
    (state : MergeState κ ν) (lo remaining runLength : Nat)
    (reverse : Bool) (inputSize naturalLength target : Nat)
    (found : FoundNewRunResult κ ν)
    (hValid : ¬(runLength = 0 ∨ remaining < runLength))
    (hFound : (foundNewRunTraced? state runLength).result = some found)
    (hSuccess : found.returnCode = 0 ∧ !found.fuelExhausted) :
    let newRun : PendingRun :=
      { base := lo
        len := BitVec.ofNat 64 runLength
        power := none }
    (listSortAfterExtensionTraced? next lo remaining reverse inputSize
      naturalLength target (state, runLength, false)).trace.policyEvents =
      (foundNewRunTraced? state runLength).trace.policyEvents ++
        [.formed
          { run := RunSpan.ofPendingRun newRun
            depthAfter := found.state.pending.size + 1
            naturalLength := naturalLength
            target := target
            remainingBefore := remaining }] ++
        (next (pushPendingRun found.state newRun) (lo + runLength)
          (remaining - runLength)).trace.policyEvents := by
  dsimp only
  simp only [listSortAfterExtensionTraced?, Bool.false_eq_true, if_false]
  rw [if_neg hValid, TraceResult.policyEvents_bind, hFound]
  simp only [hSuccess, true_and, if_true]
  rw [TraceResult.policyEvents_bind]
  have hPushResult :
      (pushFormedRunTraced found.state
        { base := lo, len := BitVec.ofNat 64 runLength, power := none }
        naturalLength target remaining).result =
        some (pushPendingRun found.state
          { base := lo, len := BitVec.ofNat 64 runLength, power := none }) :=
    erase_pushFormedRunTraced _ _ _ _ _
  rw [hPushResult]
  simp [trace_pushFormedRunTraced, AccessTrace.singletonFormedRun,
    pushPendingRun, List.append_assoc]

/-- Untraced semantic twin of the continuation after `count_run`. -/
def listSortAfterCount? (next : MergeState κ ν → Nat → Nat →
    Option (ListSortImplResult κ ν)) (state : MergeState κ ν)
    (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult κ ν) : Option (ListSortImplResult κ ν) :=
  let state := { state with data := counted.slice }
  if counted.fuelExhausted then
    finishListSort? state reverse inputSize (-1) true
  else if counted.length = 0 ∨ remaining < counted.length then
    none
  else
    let nextMinrun := minrunNext state.minrunState
    let state := installMinrunState state nextMinrun.state
    let runLength := counted.length
    let target := nextMinrun.result.toNat
    let force := if remaining ≤ target then remaining else target
    if (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result then
      match binarysort? state state.data (Int.ofNat lo) force runLength with
      | none => none
      | some sorted =>
          listSortAfterExtension? next lo remaining reverse inputSize
            ({ state with data := sorted.slice }, force, sorted.fuelExhausted)
    else
      listSortAfterExtension? next lo remaining reverse inputSize
        (state, runLength, false)

/-- Traced continuation after `count_run`; a short run delegates directly to
the genuine traced `binarysort` before entering the exported post-extension
continuation. -/
def listSortAfterCountTraced?
    (next : MergeState κ ν → Nat → Nat →
      TraceResult (ListSortImplResult κ ν))
    (state : MergeState κ ν) (lo remaining : Nat) (reverse : Bool)
    (inputSize : Nat) (counted : CountRunResult κ ν) :
    TraceResult (ListSortImplResult κ ν) :=
  let state := { state with data := counted.slice }
  if counted.fuelExhausted then
    finishListSortTraced? state reverse inputSize (-1) true
  else if counted.length = 0 ∨ remaining < counted.length then
    TraceResult.failure
  else
    let nextMinrun := minrunNext state.minrunState
    let state := installMinrunState state nextMinrun.state
    let runLength := counted.length
    let target := nextMinrun.result.toNat
    let force := if remaining ≤ target then remaining else target
    if (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result then
      (binarysortTraced? state state.data (Int.ofNat lo) force runLength).bind
        fun sorted =>
          listSortAfterExtensionTraced? next lo remaining reverse inputSize
            counted.length target
            ({ state with data := sorted.slice }, force, sorted.fuelExhausted)
    else
      listSortAfterExtensionTraced? next lo remaining reverse inputSize
        counted.length target
        (state, runLength, false)

/-- The traced run-discovery loop.  Its recursive shape and branch order mirror
`listSortScan?`; every local trace is composed at the point where the matching
C helper runs. -/
def listSortScanTraced? :
    Nat → MergeState κ ν → Nat → Nat → Bool → Nat →
      TraceResult (ListSortImplResult κ ν)
  | 0, state, _, remaining, reverse, inputSize =>
      if remaining = 0 then
        (mergeForceCollapseTraced? state).bind fun collapsed =>
          if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
            finishListSortTraced? collapsed.state reverse inputSize 0 false
          else
            failFromCollapseTraced? collapsed reverse inputSize
      else
        (finishListSortTraced? state reverse inputSize (-1) true).markFuelExhausted
  | fuel + 1, state, lo, remaining, reverse, inputSize =>
      if remaining = 0 then
        (mergeForceCollapseTraced? state).bind fun collapsed =>
          if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
            finishListSortTraced? collapsed.state reverse inputSize 0 false
          else
            failFromCollapseTraced? collapsed reverse inputSize
      else
        (countRunTraced? state state.data (Int.ofNat lo) remaining).bind fun counted =>
          listSortAfterCountTraced?
            (fun state lo remaining =>
              listSortScanTraced? fuel state lo remaining reverse inputSize)
            state lo remaining reverse inputSize counted

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
theorem listSortScanTraced_zero_fuel_active_regression :
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

/-- Genuine traced snapshot-model `list_sort_impl`.  Initial reverse-sort
instrumentation uses `sortsliceReverseTraced?`: keyed execution records the key
phase followed by the synchronized-values phase, both from the same paired
snapshot. -/
def listSortImplTraced? (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) : TraceResult (ListSortImplResult κ ν) :=
  if input.entries.size ≤ PY_LIST_MAX then
    let initialized := initialMergeState lt hasKeyfunc input
    let state := initialized.1
    let execution :=
      if !initialized.2 then
        (finishListSortTraced? state reverse input.entries.size (-1) true).markFuelExhausted
      else if input.entries.size < 2 then
        finishListSortTraced? state reverse input.entries.size 0 false
      else if reverse then
        (listSortInitialReverseTraced? state input.entries.size).bind fun reversed =>
            let state := { state with data := reversed.slice }
            if reversed.fuelExhausted then
              finishListSortTraced? state reverse input.entries.size (-1) true
            else
              listSortScanTraced? input.entries.size state 0 input.entries.size
                reverse input.entries.size
      else
        listSortScanTraced? input.entries.size state 0 input.entries.size reverse
          input.entries.size
    execution.prependMemoryEvent
      (.initial (MergeMemorySnapshot.ofState state))
  else
    TraceResult.failure

/-- Every source-admitted raw top-level execution begins with exactly the
snapshot of the state returned by `initialMergeState`.  The theorem is stated
as a head equality so later lifecycle proofs need not unfold any scan branch. -/
theorem listSortImplTraced_initial_event_head
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (hSize : input.entries.size ≤ PY_LIST_MAX) :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.memoryEvents.head? =
      some (.initial
        (MergeMemorySnapshot.ofState
          (initialMergeState lt hasKeyfunc input).1)) := by
  simp [listSortImplTraced?, hSize, TraceResult.prependMemoryEvent,
    AccessTrace.compose, AccessTrace.singletonMemoryEvent]

/-- The rejected oversize branch does not manufacture an initialization
boundary (and, as before, returns `none`). -/
theorem listSortImplTraced_oversize_no_initial_event
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (hSize : ¬ input.entries.size ≤ PY_LIST_MAX) :
    (listSortImplTraced? lt reverse hasKeyfunc input).result = none ∧
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.memoryEvents = [] := by
  simp [listSortImplTraced?, hSize, TraceResult.failure,
    AccessTrace.empty]

/-- Public traced wrapper for proof-carrying keyed or unkeyed input. -/
def listSortTraced? (lt : BoolComparator κ) (reverse : Bool)
    (input : ListSortInput κ ν) : TraceResult (ListSortImplResult κ ν) :=
  listSortImplTraced? lt reverse input.hasKeyfunc input.slice

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
theorem listSortImplTraced_formedRun_policy_regression :
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
theorem listSortImplTraced_extendedRun_policy_regression :
    (listSortImplTraced? (fun left right : Nat => decide (left < right))
      false false formedRunExtensionRegressionInput).trace.policyEvents =
      [.formed
        { run := { base := 0, len := 8 }
          depthAfter := 1
          naturalLength := 2
          target := 8
          remainingBefore := 8 }] := by
  decide

/-! ## Structural erasure -/

/-- Forgetting the final physical reverse/cleanup trace recovers the reviewed
snapshot cleanup on every modeled state, including states outside the later
source-admitted safety domain. -/
@[simp]
theorem erase_finishListSortTraced (state : MergeState κ ν) (reverse : Bool)
    (inputSize : Nat) (returnCode : Int) (fuelExhausted : Bool) :
    (finishListSortTraced? state reverse inputSize returnCode
      fuelExhausted).erase =
      finishListSort? state reverse inputSize returnCode fuelExhausted := by
  unfold finishListSortTraced? finishListSort?
  by_cases hreverse : (reverse && decide (1 < inputSize)) = true
  · rw [if_pos hreverse, if_pos hreverse]
    simp only [TraceResult.erase_bind, erase_finalReversePhaseTraced,
      sortsliceReverse?, Int.zero_add]
    cases hresult : reverseSlice? state.data 0 (Int.ofNat inputSize) <;>
      simp
  · rw [if_neg hreverse, if_neg hreverse]
    simp [TraceResult.pure, TraceResult.erase]

/-- The initial two-phase physical reverse forgets to the paired-snapshot
semantic reverse used by the raw transcription. -/
@[simp]
theorem erase_listSortInitialReverseTraced (state : MergeState κ ν)
    (inputSize : Nat) :
    (listSortInitialReverseTraced? state inputSize).erase =
      sortsliceReverse? state.data 0 inputSize := by
  exact erase_sortsliceReverseTraced state.a.hasValues state.data 0 inputSize

@[simp]
theorem erase_failFromFoundNewRunTraced (result : FoundNewRunResult κ ν)
    (reverse : Bool) (inputSize : Nat) :
    (failFromFoundNewRunTraced? result reverse inputSize).erase =
      failFromFoundNewRun? result reverse inputSize := by
  simp [failFromFoundNewRunTraced?, failFromFoundNewRun?]

@[simp]
theorem erase_failFromCollapseTraced (result : MergeForceCollapseResult κ ν)
    (reverse : Bool) (inputSize : Nat) :
    (failFromCollapseTraced? result reverse inputSize).erase =
      failFromCollapse? result reverse inputSize := by
  simp [failFromCollapseTraced?, failFromCollapse?]

/-- Erasing the post-extension continuation's helper traces recovers its
untraced semantic twin.  This is part of the internal top-level API so the
safety induction can reason branchwise without duplicating the evaluator. -/
theorem erase_listSortAfterExtensionTraced
    (nextTraced : MergeState κ ν → Nat → Nat →
      TraceResult (ListSortImplResult κ ν))
    (next : MergeState κ ν → Nat → Nat → Option (ListSortImplResult κ ν))
    (hNext : ∀ state lo remaining,
      (nextTraced state lo remaining).erase = next state lo remaining)
    (hFound : ∀ (state : MergeState κ ν) (runLength : Nat),
      (foundNewRunTraced? state runLength).erase =
        foundNewRun? state runLength)
    (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
    (naturalLength target : Nat)
    (extension : MergeState κ ν × Nat × Bool) :
    (listSortAfterExtensionTraced? nextTraced lo remaining reverse inputSize
      naturalLength target extension).erase =
      listSortAfterExtension? next lo remaining reverse inputSize extension := by
  unfold listSortAfterExtensionTraced? listSortAfterExtension?
  by_cases hfuel : extension.2.2 = true
  · rw [if_pos hfuel, if_pos hfuel, erase_finishListSortTraced]
  · rw [if_neg hfuel, if_neg hfuel]
    by_cases hinvalid : extension.2.1 = 0 ∨ remaining < extension.2.1
    · rw [if_pos hinvalid, if_pos hinvalid]
      rfl
    · rw [if_neg hinvalid, if_neg hinvalid, TraceResult.erase_bind,
        hFound]
      cases hfound : foundNewRun? extension.1 extension.2.1 with
      | none => simp
      | some found =>
          simp only [Option.bind_some]
          by_cases hsuccess :
              found.returnCode = 0 ∧ !found.fuelExhausted
          · rw [if_pos hsuccess, if_pos hsuccess,
              TraceResult.erase_bind, erase_pushFormedRunTraced]
            simpa [pushPendingRun] using
              hNext (pushPendingRun found.state
                { base := lo
                  len := BitVec.ofNat 64 extension.2.1
                  power := none })
                (lo + extension.2.1) (remaining - extension.2.1)
          · rw [if_neg hsuccess, if_neg hsuccess,
              erase_failFromFoundNewRunTraced]

/-- Erasing the post-count continuation's helper traces recovers its untraced
semantic twin, assuming erasure for the recursive continuation and
`found_new_run`. -/
theorem erase_listSortAfterCountTraced
    (nextTraced : MergeState κ ν → Nat → Nat →
      TraceResult (ListSortImplResult κ ν))
    (next : MergeState κ ν → Nat → Nat → Option (ListSortImplResult κ ν))
    (hNext : ∀ state lo remaining,
      (nextTraced state lo remaining).erase = next state lo remaining)
    (hFound : ∀ (state : MergeState κ ν) (runLength : Nat),
      (foundNewRunTraced? state runLength).erase =
        foundNewRun? state runLength)
    (state : MergeState κ ν) (lo remaining : Nat) (reverse : Bool)
    (inputSize : Nat) (counted : CountRunResult κ ν) :
    (listSortAfterCountTraced? nextTraced state lo remaining reverse inputSize
      counted).erase =
      listSortAfterCount? next state lo remaining reverse inputSize counted := by
  unfold listSortAfterCountTraced? listSortAfterCount?
  by_cases hfuel : counted.fuelExhausted = true
  · rw [if_pos hfuel, if_pos hfuel, erase_finishListSortTraced]
  · rw [if_neg hfuel, if_neg hfuel]
    by_cases hinvalid : counted.length = 0 ∨ remaining < counted.length
    · rw [if_pos hinvalid, if_pos hinvalid]
      rfl
    · rw [if_neg hinvalid, if_neg hinvalid]
      let countedState : MergeState κ ν := { state with data := counted.slice }
      let nextMinrun := minrunNext countedState.minrunState
      let installed := installMinrunState countedState nextMinrun.state
      let force := if remaining ≤ nextMinrun.result.toNat then
        remaining else nextMinrun.result.toNat
      by_cases hextend :
          ((BitVec.ofNat 64 counted.length : PySSize).slt
            nextMinrun.result) = true
      · rw [if_pos hextend, if_pos hextend, TraceResult.erase_bind,
          erase_binarysortTraced]
        cases hsorted : binarysort? installed installed.data (Int.ofNat lo)
            force counted.length with
        | none => simp
        | some sorted =>
            simp only [Option.bind_some]
            exact erase_listSortAfterExtensionTraced nextTraced next hNext
              hFound lo remaining reverse inputSize counted.length
                nextMinrun.result.toNat
                ({ installed with data := sorted.slice }, force,
                  sorted.fuelExhausted)
      · rw [if_neg hextend, if_neg hextend]
        exact erase_listSortAfterExtensionTraced nextTraced next hNext hFound
          lo remaining reverse inputSize counted.length
            nextMinrun.result.toNat (installed, counted.length, false)

private theorem listSortAfterCount_eq_scan_succ_of_count
    (fuel : Nat) (state : MergeState κ ν) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat) (counted : CountRunResult κ ν)
    (hRemaining : remaining ≠ 0)
    (hCounted : countRun? state state.data (Int.ofNat lo) remaining =
      some counted) :
    listSortAfterCount?
        (fun nextState nextLo nextRemaining =>
          listSortScan? fuel nextState nextLo nextRemaining reverse inputSize)
        state lo remaining reverse inputSize counted =
      listSortScan? (fuel + 1) state lo remaining reverse inputSize := by
  rw [listSortScan?]
  simp only [hRemaining, if_false, hCounted]
  rfl

/-- Structural top-level erasure, parameterized only by the two recursive merge
helpers whose full-domain erasure bridges are supplied by their own modules.
This formulation keeps the top-level proof independent of any safety premise:
once those instrumentation-only bridges are available, the public unconditional
corollary is immediate. -/
theorem erase_listSortScanTraced_of_helper_erasure
    (hFound : ∀ (state : MergeState κ ν) (runLength : Nat),
      (foundNewRunTraced? state runLength).erase =
        foundNewRun? state runLength)
    (hCollapse : ∀ (state : MergeState κ ν),
      (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state) :
    ∀ (fuel : Nat) (state : MergeState κ ν) (lo remaining : Nat)
      (reverse : Bool) (inputSize : Nat),
      (listSortScanTraced? fuel state lo remaining reverse inputSize).erase =
        listSortScan? fuel state lo remaining reverse inputSize := by
  intro fuel
  induction fuel with
  | zero =>
      intro state lo remaining reverse inputSize
      by_cases hremaining : remaining = 0
      · rw [listSortScanTraced?, listSortScan?, if_pos hremaining,
          if_pos hremaining, TraceResult.erase_bind, hCollapse]
        cases hcollapsed : mergeForceCollapse? state with
        | none => simp
        | some collapsed =>
            simp only [Option.bind_some]
            by_cases hsuccess :
                collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted
            · rw [if_pos hsuccess, if_pos hsuccess,
                erase_finishListSortTraced]
            · rw [if_neg hsuccess, if_neg hsuccess,
                erase_failFromCollapseTraced]
      · rw [listSortScanTraced?, listSortScan?, if_neg hremaining,
          if_neg hremaining, TraceResult.erase_markFuelExhausted,
          erase_finishListSortTraced]
  | succ fuel ih =>
      intro state lo remaining reverse inputSize
      by_cases hremaining : remaining = 0
      · rw [listSortScanTraced?, listSortScan?, if_pos hremaining,
          if_pos hremaining, TraceResult.erase_bind, hCollapse]
        cases hcollapsed : mergeForceCollapse? state with
        | none => simp
        | some collapsed =>
            simp only [Option.bind_some]
            by_cases hsuccess :
                collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted
            · rw [if_pos hsuccess, if_pos hsuccess,
                erase_finishListSortTraced]
            · rw [if_neg hsuccess, if_neg hsuccess,
                erase_failFromCollapseTraced]
      · rw [listSortScanTraced?, if_neg hremaining, TraceResult.erase_bind,
          erase_countRunTraced]
        cases hcounted : countRun? state state.data (Int.ofNat lo) remaining with
        | none =>
            rw [listSortScan?]
            rw [if_neg hremaining, hcounted]
            rfl
        | some counted =>
            simp only [Option.bind_some]
            calc
              (listSortAfterCountTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  state lo remaining reverse inputSize counted).erase =
                  listSortAfterCount?
                    (fun nextState nextLo nextRemaining =>
                      listSortScan? fuel nextState nextLo nextRemaining reverse
                        inputSize)
                    state lo remaining reverse inputSize counted :=
                erase_listSortAfterCountTraced
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  (fun nextState nextLo nextRemaining =>
                    listSortScan? fuel nextState nextLo nextRemaining reverse
                      inputSize)
                  (fun nextState nextLo nextRemaining =>
                    ih nextState nextLo nextRemaining reverse inputSize)
                  hFound state lo remaining reverse inputSize counted
              _ = listSortScan? (fuel + 1) state lo remaining reverse
                    inputSize :=
                listSortAfterCount_eq_scan_succ_of_count fuel state lo remaining
                  reverse inputSize counted hremaining hcounted

/-- Full-domain erasure for the raw top-level evaluator, parameterized by the
two recursive merge-helper erasure bridges.  No safety premise is used. -/
theorem erase_listSortImplTraced_of_helper_erasure
    (hFound : ∀ (state : MergeState κ ν) (runLength : Nat),
      (foundNewRunTraced? state runLength).erase =
        foundNewRun? state runLength)
    (hCollapse : ∀ (state : MergeState κ ν),
      (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state)
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) :
    (listSortImplTraced? lt reverse hasKeyfunc input).erase =
      listSortImpl? lt reverse hasKeyfunc input := by
  unfold listSortImplTraced? listSortImpl?
  by_cases hsize : input.entries.size ≤ PY_LIST_MAX
  · rw [if_pos hsize, if_pos hsize,
      TraceResult.erase_prependMemoryEvent]
    let initialized := initialMergeState lt hasKeyfunc input
    let state := initialized.1
    by_cases hinit : (!initialized.2) = true
    · rw [if_pos hinit, if_pos hinit,
        TraceResult.erase_markFuelExhausted, erase_finishListSortTraced]
    · rw [if_neg hinit, if_neg hinit]
      by_cases hsmall : input.entries.size < 2
      · rw [if_pos hsmall, if_pos hsmall, erase_finishListSortTraced]
      · rw [if_neg hsmall, if_neg hsmall]
        by_cases hreverse : reverse = true
        · rw [if_pos hreverse, if_pos hreverse, TraceResult.erase_bind,
            erase_listSortInitialReverseTraced]
          cases hreversed : sortsliceReverse? state.data 0 input.entries.size with
          | none => simp
          | some reversed =>
              simp only [Option.bind_some]
              by_cases hfuel : reversed.fuelExhausted = true
              · rw [if_pos hfuel, if_pos hfuel,
                  erase_finishListSortTraced]
              · rw [if_neg hfuel, if_neg hfuel]
                exact erase_listSortScanTraced_of_helper_erasure hFound
                  hCollapse input.entries.size
                  { state with data := reversed.slice } 0 input.entries.size
                  reverse input.entries.size
        · rw [if_neg hreverse, if_neg hreverse]
          exact erase_listSortScanTraced_of_helper_erasure hFound hCollapse
            input.entries.size state 0 input.entries.size reverse
            input.entries.size
  · rw [if_neg hsize, if_neg hsize]
    rfl

/-- Full-domain erasure for the proof-carrying public wrapper, still stated
against explicit helper-erasure assumptions until their raw-domain bridge
module is imported. -/
theorem erase_listSortTraced_of_helper_erasure
    (hFound : ∀ (state : MergeState κ ν) (runLength : Nat),
      (foundNewRunTraced? state runLength).erase =
        foundNewRun? state runLength)
    (hCollapse : ∀ (state : MergeState κ ν),
      (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state)
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν) :
    (listSortTraced? lt reverse input).erase = listSort? lt reverse input := by
  exact erase_listSortImplTraced_of_helper_erasure hFound hCollapse lt reverse
    input.hasKeyfunc input.slice

end CPythonListsort

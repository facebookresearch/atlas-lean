/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeAtSafety
import Code.Policy.MergeForceCollapsePreservation

/-!
# `merge_force_collapse` safety

This module traces the neighboring pending-run reads performed by the reviewed
sequential Lean transcription of `merge_force_collapse` and composes them with
the complete trace of each delegated `merge_at` call.  This is an exact order
claim about the Lean model; it does not impose an evaluation order on the two
operands of C's `<` operator.  The public safety theorem proves that the
pending-depth fuel supplied by the transcription is adequate for every
nonempty valid layout.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

private def mergeForceCollapseSuccessResult (state : MergeState κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def mergeForceCollapseOutOfFuelResult (state : MergeState κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

private def mergeForceCollapseFromMergeAt (result : MergeAtResult κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Traced form of the source's merge-position choice.  When there are at
least three pending runs, the reviewed sequential Lean model records the lower
neighbor and then the upper neighbor.  This is not a claim about C operand
evaluation order. -/
def forceCollapseIndexTraced? (state : MergeState κ ν) : TraceResult Nat :=
  if 1 < state.pending.size then
    let i := state.pending.size - 2
    if 0 < i then
      (TraceResult.pendingRunRead? state (Int.ofNat (i - 1))).bind fun previous =>
        (TraceResult.pendingRunRead? state (Int.ofNat (i + 1))).map fun following =>
          if previous.len.slt following.len then i - 1 else i
    else
      TraceResult.pure i
  else
    TraceResult.failure

/-- Fuel-bounded traced collapse loop.  Exhaustion is observable both in its
result and in the trace. -/
def mergeForceCollapseLoopTraced? :
    Nat → MergeState κ ν → TraceResult (MergeForceCollapseResult κ ν)
  | 0, state =>
      if state.pending.size ≤ 1 then
        TraceResult.pure (mergeForceCollapseSuccessResult state)
      else
        (TraceResult.pure
          (mergeForceCollapseOutOfFuelResult state)).markFuelExhausted
  | fuel + 1, state =>
      if 1 < state.pending.size then
        (forceCollapseIndexTraced? state).bind fun i =>
          (mergeAtTraced? state i).bind fun merged =>
            if merged.returnCode = 0 ∧ !merged.fuelExhausted then
              mergeForceCollapseLoopTraced? fuel merged.state
            else
              TraceResult.pure (mergeForceCollapseFromMergeAt merged)
      else
        TraceResult.pure (mergeForceCollapseSuccessResult state)

/-- Fully traced `merge_force_collapse` evaluator. -/
def mergeForceCollapseTraced? (state : MergeState κ ν) :
    TraceResult (MergeForceCollapseResult κ ν) :=
  mergeForceCollapseLoopTraced? state.pending.size state

private theorem TraceResult.bind_result_of_eq_some
    (current : TraceResult α) (next : α → TraceResult β) (value : α)
    (hresult : current.result = some value) :
    (current.bind next).result = (next value).result := by
  change (current.bind next).erase = (next value).erase
  rw [TraceResult.erase_bind]
  change current.result.bind (fun item => (next item).result) = _
  rw [hresult]
  rfl

private theorem pendingRunRead_result_of_bounds (state : MergeState κ ν)
    (index : Nat) (hindex : index < state.pending.size) :
    (TraceResult.pendingRunRead? state (Int.ofNat index)).result =
      some state.pending[index] := by
  change (TraceResult.pendingRunRead? state (Int.ofNat index)).erase = _
  rw [TraceResult.erase_pendingRunRead]
  have hnonnegative : 0 ≤ Int.ofNat index := Int.natCast_nonneg _
  rw [if_pos hnonnegative]
  have htoi : (Int.ofNat index).toNat = index := rfl
  rw [htoi]
  exact Array.getElem?_eq_getElem hindex

private theorem pendingRunRead_safe (state : MergeState κ ν) (index : Nat)
    (hindex : index < state.pending.size) :
    MovementTraceSafe
      (TraceResult.pendingRunRead? state (Int.ofNat index)) := by
  constructor
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_pendingRunRead]
    simp only [AccessTrace.allAccessesInBounds,
      AccessTrace.singletonAccess, List.mem_singleton,
      forall_eq, AccessEvent.InBounds]
    exact ⟨Int.natCast_nonneg _, (Int.ofNat_lt).mpr hindex⟩
  · simp [TraceResult.trace_pendingRunRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

/-- Erasing the selector trace recovers the reviewed transcription exactly. -/
@[simp]
theorem erase_forceCollapseIndexTraced (state : MergeState κ ν) :
    (forceCollapseIndexTraced? state).erase = forceCollapseIndex? state := by
  unfold forceCollapseIndexTraced? forceCollapseIndex?
  by_cases hmany : 1 < state.pending.size
  · simp only [hmany, if_true]
    let i := state.pending.size - 2
    by_cases hpositive : 0 < i
    · have hlower : i - 1 < state.pending.size := by omega
      have hupper : i + 1 < state.pending.size := by
        dsimp [i]
        omega
      let previous := state.pending[i - 1]
      let following := state.pending[i + 1]
      have hprevious : state.pending[i - 1]? = some previous :=
        Array.getElem?_eq_getElem hlower
      have hfollowing : state.pending[i + 1]? = some following :=
        Array.getElem?_eq_getElem hupper
      have hpositive' : 0 < state.pending.size - 2 := by
        simpa [i] using hpositive
      rw [if_pos hpositive']
      simp only [TraceResult.erase_bind, TraceResult.erase_pendingRunRead]
      have hlowerNonnegative : 0 ≤ Int.ofNat (i - 1) := Int.natCast_nonneg _
      rw [if_pos hlowerNonnegative]
      have hlowerToNat : (Int.ofNat (i - 1)).toNat = i - 1 := rfl
      rw [hlowerToNat, hprevious]
      rw [if_pos hpositive']
      simp only [Option.bind_some, TraceResult.erase_map,
        TraceResult.erase_pendingRunRead]
      have hupperNonnegative :
          0 ≤ Int.ofNat (state.pending.size - 2 + 1) := Int.natCast_nonneg _
      rw [if_pos hupperNonnegative]
      have hupperToNat :
          (Int.ofNat (state.pending.size - 2 + 1)).toNat =
            state.pending.size - 2 + 1 := rfl
      rw [hupperToNat]
      have hfollowing' :
          state.pending[state.pending.size - 2 + 1]? = some following := by
        simpa [i] using hfollowing
      rw [hfollowing']
      simp only [Option.map_some]
      by_cases hcomparison : previous.len.slt following.len <;>
        simp [hcomparison]
    · have hnotThree : ¬2 < state.pending.size := by
        dsimp [i] at hpositive
        omega
      simp [hnotThree]
  · simp [hmany, TraceResult.erase_failure]

/-- The neighboring-length selector performs ordinary pending-stack reads but
never emits a merge-memory lifecycle boundary. -/
theorem forceCollapseIndexTraced_memoryEvents_eq_nil
    (state : MergeState κ ν) :
    (forceCollapseIndexTraced? state).trace.memoryEvents = [] := by
  unfold forceCollapseIndexTraced?
  by_cases hmany : 1 < state.pending.size
  · rw [if_pos hmany]
    dsimp only
    by_cases hpositive : 0 < state.pending.size - 2
    · rw [if_pos hpositive]
      apply TraceResult.memoryEvents_bind_eq_nil
      · simp [TraceResult.trace_pendingRunRead,
          AccessTrace.singletonAccess]
      · intro previous
        simp [TraceResult.memoryEvents_map,
          TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
    · rw [if_neg hpositive]
      rfl
  · rw [if_neg hmany]
    rfl

/-- The event-free selector is the identity merge-memory segment on its
caller's concrete storage snapshot. -/
theorem forceCollapseIndexTraced_memorySegment
    (state : MergeState κ ν) :
    (forceCollapseIndexTraced? state).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState state)
      (MergeMemorySnapshot.ofState state) := by
  refine ⟨[], ?_, ?_⟩
  · simpa using forceCollapseIndexTraced_memoryEvents_eq_nil state
  · rfl

/-- On every loop iteration the selector succeeds, reads only live pending
entries, and returns exactly one of CPython's two allowed merge positions. -/
theorem forceCollapseIndexTraced_safe (state : MergeState κ ν)
    (hmany : 1 < state.pending.size) :
    ∃ i,
      (forceCollapseIndexTraced? state).result = some i ∧
      MovementTraceSafe (forceCollapseIndexTraced? state) ∧
      (forceCollapseIndexTraced? state).erase = forceCollapseIndex? state ∧
      (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) := by
  let topPair := state.pending.size - 2
  by_cases hpositive : 0 < topPair
  · have hlower : topPair - 1 < state.pending.size := by omega
    have hupper : topPair + 1 < state.pending.size := by
      dsimp [topPair]
      omega
    let previous := state.pending[topPair - 1]
    let following := state.pending[topPair + 1]
    have hprevious :
        (TraceResult.pendingRunRead? state
          (Int.ofNat (topPair - 1))).result = some previous :=
      pendingRunRead_result_of_bounds state _ hlower
    have hfollowing :
        (TraceResult.pendingRunRead? state
          (Int.ofNat (topPair + 1))).result = some following :=
      pendingRunRead_result_of_bounds state _ hupper
    have hpreviousSafe := pendingRunRead_safe state (topPair - 1) hlower
    have hfollowingSafe := pendingRunRead_safe state (topPair + 1) hupper
    have hselectorSafe : MovementTraceSafe
        ((TraceResult.pendingRunRead? state
          (Int.ofNat (topPair - 1))).bind fun previous =>
            (TraceResult.pendingRunRead? state
              (Int.ofNat (topPair + 1))).map fun following =>
                if previous.len.slt following.len then topPair - 1
                else topPair) := by
      apply MovementTraceSafe.bind _ _ previous hprevious hpreviousSafe
      exact MovementTraceSafe.map _ _ hfollowingSafe
    by_cases hlowerChosen : previous.len.slt following.len
    · refine ⟨topPair - 1, ?_, ?_, erase_forceCollapseIndexTraced state, ?_⟩
      · unfold forceCollapseIndexTraced?
        simp only [hmany, hpositive, if_true, topPair]
        rw [TraceResult.bind_result_of_eq_some _ _ previous hprevious]
        change Option.map _ _ = _
        rw [hfollowing]
        simp [hlowerChosen]
      · simpa [forceCollapseIndexTraced?, hmany, hpositive, topPair] using
          hselectorSafe
      · right
        dsimp [topPair]
        omega
    · refine ⟨topPair, ?_, ?_, erase_forceCollapseIndexTraced state, ?_⟩
      · unfold forceCollapseIndexTraced?
        simp only [hmany, hpositive, if_true, topPair]
        rw [TraceResult.bind_result_of_eq_some _ _ previous hprevious]
        change Option.map _ _ = _
        rw [hfollowing]
        simp [hlowerChosen]
      · simpa [forceCollapseIndexTraced?, hmany, hpositive, topPair] using
          hselectorSafe
      · left
        dsimp [topPair]
        omega
  · have htopPair : topPair = 0 := by omega
    have hsize : state.pending.size = 2 := by
      dsimp [topPair] at hpositive
      omega
    refine ⟨0, ?_, ?_, erase_forceCollapseIndexTraced state, ?_⟩
    · simp [forceCollapseIndexTraced?, hsize]
      rfl
    · simpa [forceCollapseIndexTraced?, hsize] using
        (MovementTraceSafe.pure (0 : Nat))
    · left
      dsimp [topPair] at htopPair
      omega

/-- With at least three pending runs, the selector observes precisely the two
neighboring lengths in the reviewed sequential Lean transcription's order.
This does not assert a C-language operand evaluation order. -/
theorem forceCollapseIndexTraced_neighbor_access_order
    (state : MergeState κ ν) (hthree : 2 < state.pending.size) :
    (forceCollapseIndexTraced? state).trace.accesses =
      [{ kind := .read, region := .pendingRuns,
          index := Int.ofNat (state.pending.size - 3),
          extent := state.pending.size },
       { kind := .read, region := .pendingRuns,
          index := Int.ofNat (state.pending.size - 1),
          extent := state.pending.size }] := by
  have hmany : 1 < state.pending.size := by omega
  have hlower : state.pending.size - 3 < state.pending.size := by omega
  let previous := state.pending[state.pending.size - 3]
  have hprevious :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 3))).result =
        some previous := pendingRunRead_result_of_bounds state _ hlower
  unfold forceCollapseIndexTraced?
  rw [if_pos hmany]
  dsimp only
  have hpositive : 0 < state.pending.size - 2 := by omega
  rw [if_pos hpositive]
  have hlowerEq : state.pending.size - 2 - 1 =
      state.pending.size - 3 := by omega
  have hupperEq : state.pending.size - 2 + 1 =
      state.pending.size - 1 := by omega
  rw [hlowerEq, hupperEq]
  simp only [TraceResult.trace_bind, hprevious,
    TraceResult.trace_pendingRunRead, TraceResult.map, AccessTrace.compose,
    AccessTrace.singletonAccess]
  rfl

/-- A two-run stack takes the top-pair branch without reading neighboring
length records; the delegated `merge_at` performs its own traced accesses. -/
theorem forceCollapseIndexTraced_two_runs
    (state : MergeState κ ν) (hsize : state.pending.size = 2) :
    (forceCollapseIndexTraced? state).result = some 0 ∧
      (forceCollapseIndexTraced? state).trace.accesses = [] := by
  simp [forceCollapseIndexTraced?, hsize, TraceResult.pure,
    AccessTrace.empty]

/-- The trace of a successful iteration contains the selector observations,
the complete delegated `merge_at` trace, and the recursive trace in exactly
that order. -/
theorem mergeForceCollapseLoopTraced_merge_trace_order
    (fuel : Nat) (state : MergeState κ ν) (i : Nat)
    (merged : MergeAtResult κ ν)
    (hmany : 1 < state.pending.size)
    (hindex : (forceCollapseIndexTraced? state).result = some i)
    (hmerge : (mergeAtTraced? state i).result = some merged)
    (hsuccess : merged.returnCode = 0 ∧ !merged.fuelExhausted) :
    (mergeForceCollapseLoopTraced? (fuel + 1) state).trace =
      (forceCollapseIndexTraced? state).trace.compose
        ((mergeAtTraced? state i).trace.compose
          (mergeForceCollapseLoopTraced? fuel merged.state).trace) := by
  simp only [mergeForceCollapseLoopTraced?, hmany, if_true,
    TraceResult.trace_bind, hindex, hmerge]
  rw [if_pos hsuccess]

/-- Replacing one selected adjacent pair by one merged run decrements the
pending depth by exactly one, so predecessor fuel is exactly the next depth. -/
theorem mergeForceCollapseLoop_fuel_tracks_merge
    (fuel : Nat) (state afterState : MergeState κ ν)
    (before after : List PendingRun) (left right merged : PendingRun)
    (hfuel : fuel + 1 = state.pending.size)
    (hbefore :
      state.pending.toList = before ++ left :: right :: after)
    (hafter :
      afterState.pending.toList = before ++ merged :: after) :
    fuel = afterState.pending.size := by
  have hbeforeSize := congrArg List.length hbefore
  have hafterSize := congrArg List.length hafter
  simp only [Array.length_toList, List.length_append,
    List.length_cons] at hbeforeSize hafterSize
  omega

/-- A positive-fuel singleton execution is the normal success arm: it performs
no indexed access and does not mark fuel exhaustion. -/
theorem mergeForceCollapseLoopTraced_singleton_no_access
    (fuel : Nat) (state : MergeState κ ν)
    (hsize : state.pending.size = 1) :
    (mergeForceCollapseLoopTraced? (fuel + 1) state).result.map
        (fun result => (result.returnCode, result.fuelExhausted)) =
      some (0, false) ∧
    (mergeForceCollapseLoopTraced? (fuel + 1) state).trace.accesses = [] ∧
    (mergeForceCollapseLoopTraced? (fuel + 1)
      state).trace.fuelExhausted = false := by
  simp [mergeForceCollapseLoopTraced?, hsize,
    mergeForceCollapseSuccessResult, TraceResult.pure, AccessTrace.empty]

/-- The complete evaluator's empty and singleton fast paths both succeed
without indexed accesses or a synthetic fuel marker. -/
theorem mergeForceCollapseTraced_small_no_access
    (state : MergeState κ ν) (hsmall : state.pending.size ≤ 1) :
    (mergeForceCollapseTraced? state).result.map
        (fun result => (result.returnCode, result.fuelExhausted)) =
      some (0, false) ∧
    (mergeForceCollapseTraced? state).trace.accesses = [] ∧
    (mergeForceCollapseTraced? state).trace.fuelExhausted = false := by
  by_cases hempty : state.pending.size = 0
  · simp [mergeForceCollapseTraced?, hempty,
      mergeForceCollapseLoopTraced?, mergeForceCollapseSuccessResult,
      TraceResult.pure, AccessTrace.empty]
  · have hsingleton : state.pending.size = 1 := by omega
    simpa [mergeForceCollapseTraced?, hsingleton] using
      mergeForceCollapseLoopTraced_singleton_no_access 0 state hsingleton

/-- The independently observable zero-fuel arm erases to the same exhausted
result as the reviewed loop transcription. -/
@[simp]
theorem erase_mergeForceCollapseLoopTraced_zero
    (state : MergeState κ ν) :
    (mergeForceCollapseLoopTraced? 0 state).erase =
      mergeForceCollapseLoop? 0 state := by
  simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?]
  by_cases hsmall : state.pending.size ≤ 1
  · rw [if_pos hsmall, if_pos hsmall, TraceResult.erase_pure]
    rfl
  · rw [if_neg hsmall, if_neg hsmall,
      TraceResult.erase_markFuelExhausted, TraceResult.erase_pure]
    rfl

/-- State fields which the collapse loop is forbidden to mutate. -/
structure MergeForceCollapseStableFrame
    (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeForceCollapseStableFrame

theorem refl (state : MergeState κ ν) :
    MergeForceCollapseStableFrame state state := by
  constructor <;> rfl

theorem trans {first second third : MergeState κ ν}
    (hfirst : MergeForceCollapseStableFrame first second)
    (hsecond : MergeForceCollapseStableFrame second third) :
    MergeForceCollapseStableFrame first third := by
  exact
    { listlen := hsecond.listlen.trans hfirst.listlen
      basekeys := hsecond.basekeys.trans hfirst.basekeys
      dataSize := hsecond.dataSize.trans hfirst.dataSize
      tempValuesMode := hsecond.tempValuesMode.trans hfirst.tempValuesMode
      comparator := hsecond.comparator.trans hfirst.comparator
      mrCurrent := hsecond.mrCurrent.trans hfirst.mrCurrent
      mrE := hsecond.mrE.trans hfirst.mrE
      mrMask := hsecond.mrMask.trans hfirst.mrMask }

theorem of_mergeAt {before after : MergeState κ ν}
    (h : MergeAtStableFrame before after) :
    MergeForceCollapseStableFrame before after := by
  exact
    { listlen := h.listlen
      basekeys := h.basekeys
      dataSize := h.dataSize
      tempValuesMode := h.tempValuesMode
      comparator := h.comparator
      mrCurrent := h.mrCurrent
      mrE := h.mrE
      mrMask := h.mrMask }

end MergeForceCollapseStableFrame

private structure MergeForceCollapseLoopSafetyPost
    (pre : MergeState κ ν) (scanned fuel : Nat)
    (result : MergeForceCollapseResult κ ν) : Prop where
  resultEq :
    (mergeForceCollapseLoopTraced? fuel pre).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe (mergeForceCollapseLoopTraced? fuel pre)
  exactErasure :
    (mergeForceCollapseLoopTraced? fuel pre).erase =
      mergeForceCollapseLoop? fuel pre
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  memoryEventsValid :
    (mergeForceCollapseLoopTraced? fuel pre).trace.memoryEventsValid
      pre.a.hasValues
  onlyMergeMemoryEvents :
    (mergeForceCollapseLoopTraced? fuel pre).trace.onlyMergeMemoryEvents
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (mergeForceCollapseLoopTraced? fuel pre).trace.mergeMemoryEventsBounded
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound
  memorySegment :
    (mergeForceCollapseLoopTraced? fuel pre).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState pre)
      (MergeMemorySnapshot.ofState result.state)
  stableFrame : MergeForceCollapseStableFrame pre result.state
  pendingLayout : PendingLayout result.state scanned
  singleton : ∃ run, result.state.pending.toList = [run]

private theorem mergeForceCollapseLoopTraced_safe
    (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
    (hfuel : fuel = state.pending.size)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hnonempty : state.pending.toList ≠ [])
    (hlayout : PendingLayout state scanned)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result,
      MergeForceCollapseLoopSafetyPost state scanned fuel result := by
  induction fuel generalizing state with
  | zero =>
      have hsizePositive : 0 < state.pending.size := by
        have := List.length_pos_of_ne_nil hnonempty
        simpa using this
      omega
  | succ remaining ih =>
      by_cases hmany : 1 < state.pending.size
      · rcases forceCollapseIndexTraced_safe state hmany with
          ⟨i, hindexResult, hindexSafe, hindexErasure, hposition⟩
        rcases mergeAt_safe state scanned i hlayout hmax hposition hInv hLive
            hMode with ⟨merged, hmerge⟩
        have hmergeSafe : MovementTraceSafe (mergeAtTraced? state i) :=
          ⟨hmerge.traceFuel, hmerge.noPushes, hmerge.accessesInBounds,
            hmerge.tempAccessesLive⟩
        have hmergeRaw : mergeAt? state i = some merged := by
          rw [← hmerge.exactErasure]
          exact hmerge.resultEq
        rcases mergeAt_preserves_pendingLayout state scanned i merged hlayout
            hmergeRaw with
          ⟨before, left, right, after, hbeforeLength, hbeforePending,
            hafterPending, _hleftNonnegative, _hleftPositive,
            _hrightNonnegative, _hrightPositive, _hadjacent, _hsum,
            hmergedLayout⟩
        have hnextFuel : remaining = merged.state.pending.size :=
          mergeForceCollapseLoop_fuel_tracks_merge remaining state
            merged.state before after left right
            ({ left with len := left.len + right.len } : PendingRun)
            hfuel hbeforePending hafterPending
        have hmergedNonempty : merged.state.pending.toList ≠ [] := by
          rw [hafterPending]
          simp
        have hmergedMax : merged.state.listlen.toNat ≤ PY_LIST_MAX := by
          rw [hmerge.stableFrame.listlen]
          exact hmax
        rcases ih merged.state hnextFuel hmergedMax hmergedNonempty
            hmergedLayout hmerge.tempInvariant hmerge.tempLive
            hmerge.valuesMode with ⟨result, hrest⟩
        have hsuccess :
            merged.returnCode = 0 ∧ !merged.fuelExhausted := by
          exact ⟨hmerge.returnCode, by simp [hmerge.resultFuel]⟩
        have htailSafe : MovementTraceSafe
            ((mergeAtTraced? state i).bind fun merged =>
              if merged.returnCode = 0 ∧ !merged.fuelExhausted then
                mergeForceCollapseLoopTraced? remaining merged.state
              else
                TraceResult.pure
                  (mergeForceCollapseFromMergeAt merged)) := by
          apply MovementTraceSafe.bind _ _ merged hmerge.resultEq hmergeSafe
          rw [if_pos hsuccess]
          exact hrest.traceSafe
        have hfullSafe : MovementTraceSafe
            (mergeForceCollapseLoopTraced? (remaining + 1) state) := by
          simp only [mergeForceCollapseLoopTraced?, hmany, if_true]
          exact MovementTraceSafe.bind _ _ i hindexResult hindexSafe htailSafe
        have hresult :
            (mergeForceCollapseLoopTraced? (remaining + 1) state).result =
              some result := by
          simp only [mergeForceCollapseLoopTraced?, hmany, if_true]
          rw [TraceResult.bind_result_of_eq_some _ _ i hindexResult]
          rw [TraceResult.bind_result_of_eq_some _ _ merged hmerge.resultEq]
          rw [if_pos hsuccess]
          exact hrest.resultEq
        have hexact :
            (mergeForceCollapseLoopTraced? (remaining + 1) state).erase =
              mergeForceCollapseLoop? (remaining + 1) state := by
          simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?,
            hmany, if_true, TraceResult.erase_bind]
          rw [hindexErasure]
          have hindexRaw : forceCollapseIndex? state = some i := by
            rw [← hindexErasure]
            exact hindexResult
          rw [hindexRaw]
          simp only [Option.bind_some]
          rw [hmerge.exactErasure, hmergeRaw]
          simp only [Option.bind_some, if_pos hsuccess]
          exact hrest.exactErasure
        have htraceOrder :
            (mergeForceCollapseLoopTraced? (remaining + 1) state).trace =
              (forceCollapseIndexTraced? state).trace.compose
                ((mergeAtTraced? state i).trace.compose
                  (mergeForceCollapseLoopTraced? remaining
                    merged.state).trace) :=
          mergeForceCollapseLoopTraced_merge_trace_order remaining state i
            merged hmany hindexResult hmerge.resultEq hsuccess
        refine ⟨result, ?_⟩
        exact
          { resultEq := hresult
            returnCode := hrest.returnCode
            resultFuel := hrest.resultFuel
            traceSafe := hfullSafe
            exactErasure := hexact
            tempInvariant := hrest.tempInvariant
            tempLive := hrest.tempLive
            valuesMode := hrest.valuesMode
            hasValuesFrame := hrest.hasValuesFrame.trans
              hmerge.hasValuesFrame
            memoryEventsValid := by
              rw [htraceOrder,
                AccessTrace.memoryEventsValid_compose,
                AccessTrace.memoryEventsValid_compose]
              refine ⟨?_, hmerge.memoryEventsValid, ?_⟩
              · simp [AccessTrace.memoryEventsValid,
                  forceCollapseIndexTraced_memoryEvents_eq_nil]
              · simpa [hmerge.hasValuesFrame] using
                  hrest.memoryEventsValid
            onlyMergeMemoryEvents := by
              rw [htraceOrder,
                AccessTrace.onlyMergeMemoryEvents_compose,
                AccessTrace.onlyMergeMemoryEvents_compose]
              refine ⟨?_, hmerge.onlyMergeMemoryEvents,
                hrest.onlyMergeMemoryEvents⟩
              simp [AccessTrace.onlyMergeMemoryEvents,
                forceCollapseIndexTraced_memoryEvents_eq_nil]
            memoryEventsBounded := by
              intro hbound
              rw [htraceOrder,
                AccessTrace.mergeMemoryEventsBounded_compose,
                AccessTrace.mergeMemoryEventsBounded_compose]
              refine ⟨?_, hmerge.memoryEventsBounded hbound, ?_⟩
              · simp [AccessTrace.mergeMemoryEventsBounded,
                  forceCollapseIndexTraced_memoryEvents_eq_nil]
              · exact hrest.memoryEventsBounded
                  (hmerge.physicalSlotsBound hbound)
            physicalSlotsBound := by
              intro hbound
              exact hrest.physicalSlotsBound
                (hmerge.physicalSlotsBound hbound)
            memorySegment := by
              rw [htraceOrder]
              exact AccessTrace.mergeMemorySegment_compose _ _ _ _ _
                (forceCollapseIndexTraced_memorySegment state)
                (AccessTrace.mergeMemorySegment_compose _ _ _ _ _
                  hmerge.memorySegment hrest.memorySegment)
            stableFrame :=
              (MergeForceCollapseStableFrame.of_mergeAt hmerge.stableFrame).trans
                hrest.stableFrame
            pendingLayout := hrest.pendingLayout
            singleton := hrest.singleton }
      · have hsizeOne : state.pending.size = 1 := by
          have hsizePositive : 0 < state.pending.size := by
            have := List.length_pos_of_ne_nil hnonempty
            simpa using this
          omega
        have hlistLength : state.pending.toList.length = 1 := by
          simpa only [Array.length_toList] using hsizeOne
        rcases List.length_eq_one_iff.mp hlistLength with ⟨run, hruns⟩
        let result := mergeForceCollapseSuccessResult state
        have hpure : MovementTraceSafe (TraceResult.pure result) :=
          MovementTraceSafe.pure result
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp only [mergeForceCollapseLoopTraced?, hmany, if_false]
              change (TraceResult.pure result).result = some result
              rfl
            returnCode := rfl
            resultFuel := rfl
            traceSafe := by
              simpa [mergeForceCollapseLoopTraced?, hmany, result] using hpure
            exactErasure := by
              simp only [mergeForceCollapseLoopTraced?,
                mergeForceCollapseLoop?, hmany, if_false,
                TraceResult.erase_pure]
              rfl
            tempInvariant := hInv
            tempLive := hLive
            valuesMode := hMode
            hasValuesFrame := rfl
            memoryEventsValid := by
              simp [mergeForceCollapseLoopTraced?, hmany,
                AccessTrace.memoryEventsValid, TraceResult.pure,
                AccessTrace.empty]
            onlyMergeMemoryEvents := by
              simp [mergeForceCollapseLoopTraced?, hmany,
                AccessTrace.onlyMergeMemoryEvents, TraceResult.pure,
                AccessTrace.empty]
            memoryEventsBounded := by
              intro _
              simp [mergeForceCollapseLoopTraced?, hmany,
                AccessTrace.mergeMemoryEventsBounded, TraceResult.pure,
                AccessTrace.empty]
            physicalSlotsBound := fun hbound => hbound
            memorySegment := by
              refine ⟨[], ?_, ?_⟩
              · simp [mergeForceCollapseLoopTraced?, hmany,
                  TraceResult.pure, AccessTrace.empty]
              · rfl
            stableFrame := MergeForceCollapseStableFrame.refl state
            pendingLayout := hlayout
            singleton := ⟨run, hruns⟩ }

/-- Full public postcondition for a source-admitted final collapse. -/
structure MergeForceCollapseSafetyPost
    (pre : MergeState κ ν) (scanned : Nat)
    (result : MergeForceCollapseResult κ ν) : Prop where
  resultEq : (mergeForceCollapseTraced? pre).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (mergeForceCollapseTraced? pre).trace.fuelExhausted = false
  accessesInBounds :
    (mergeForceCollapseTraced? pre).trace.allAccessesInBounds
  tempAccessesLive :
    (mergeForceCollapseTraced? pre).trace.tempPayloadAccessesLive
  noPushes : (mergeForceCollapseTraced? pre).trace.pushDepths = []
  exactErasure :
    (mergeForceCollapseTraced? pre).erase = mergeForceCollapse? pre
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  memoryEventsValid :
    (mergeForceCollapseTraced? pre).trace.memoryEventsValid pre.a.hasValues
  onlyMergeMemoryEvents :
    (mergeForceCollapseTraced? pre).trace.onlyMergeMemoryEvents
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (mergeForceCollapseTraced? pre).trace.mergeMemoryEventsBounded
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound
  memorySegment :
    (mergeForceCollapseTraced? pre).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState pre)
      (MergeMemorySnapshot.ofState result.state)
  stableFrame : MergeForceCollapseStableFrame pre result.state
  pendingLayout : PendingLayout result.state scanned
  singleton : ∃ run, result.state.pending.toList = [run]
  finalRun : ∃ run,
    result.state.pending.toList = [run] ∧
      run.base = pre.basekeys ∧
      run.endIndex = pre.basekeys + scanned

/-- End-to-end safety of `merge_force_collapse` on its source-admitted domain.
The pending depth is adequate fuel, all selector and delegated accesses remain
in bounds, temporary payload accesses observe live backing, and the final
state retains the active storage and values-mode invariants. -/
theorem mergeForceCollapse_safe
    (state : MergeState κ ν) (scanned : Nat)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hnonempty : state.pending.toList ≠ [])
    (hlayout : PendingLayout state scanned)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result, MergeForceCollapseSafetyPost state scanned result := by
  rcases mergeForceCollapseLoopTraced_safe state.pending.size state scanned rfl
      hmax hnonempty hlayout hInv hLive hMode with ⟨result, hresult⟩
  have hraw : mergeForceCollapse? state = some result := by
    unfold mergeForceCollapse?
    rw [← hresult.exactErasure]
    exact hresult.resultEq
  rcases mergeForceCollapse_preserves_pendingLayout state scanned result
      hnonempty hlayout hraw hresult.returnCode hresult.resultFuel with
    ⟨_hlistlen, _hbasekeys, _hdataSize, _hresultLayout, run,
      hpending, hbase, hend⟩
  refine ⟨result, ?_⟩
  exact
    { resultEq := hresult.resultEq
      returnCode := hresult.returnCode
      resultFuel := hresult.resultFuel
      traceFuel := hresult.traceSafe.fuel
      accessesInBounds := hresult.traceSafe.bounds
      tempAccessesLive := hresult.traceSafe.tempLive
      noPushes := hresult.traceSafe.noPushes
      exactErasure := hresult.exactErasure
      tempInvariant := hresult.tempInvariant
      tempLive := hresult.tempLive
      valuesMode := hresult.valuesMode
      hasValuesFrame := hresult.hasValuesFrame
      memoryEventsValid := hresult.memoryEventsValid
      onlyMergeMemoryEvents := hresult.onlyMergeMemoryEvents
      memoryEventsBounded := hresult.memoryEventsBounded
      physicalSlotsBound := hresult.physicalSlotsBound
      memorySegment := hresult.memorySegment
      stableFrame := hresult.stableFrame
      pendingLayout := hresult.pendingLayout
      singleton := hresult.singleton
      finalRun := ⟨run, hpending, hbase, hend⟩ }

/-- On the source-admitted domain, erasing the genuine composed trace recovers
the reviewed `mergeForceCollapse?` execution exactly.  The scope is explicit:
the delegated `merge_at` safety contract establishes its own exact erasure on
the same invariant-bearing call path. -/
theorem erase_mergeForceCollapseTraced_of_admitted
    (state : MergeState κ ν) (scanned : Nat)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hnonempty : state.pending.toList ≠ [])
    (hlayout : PendingLayout state scanned)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state := by
  rcases mergeForceCollapse_safe state scanned hmax hnonempty hlayout hInv
      hLive hMode with ⟨_result, hresult⟩
  exact hresult.exactErasure

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
theorem forceCollapseIndexTraced_two_run_regression :
    forceCollapseIndexTraced? forceCollapseTwoRegressionState =
      { result := some 0, trace := AccessTrace.empty } := by
  decide

private def forceCollapseEmptyRegressionState : MergeState Nat Nat :=
  { forceCollapseTwoRegressionState with pending := #[] }

/-- The selector's out-of-loop failure arm is observable on a concrete empty
stack and agrees with `forceCollapseIndex? = none`; the collapse loop itself
short-circuits before calling this arm. -/
theorem forceCollapseIndexTraced_empty_failure_regression :
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
theorem forceCollapseIndexTraced_lower_branch_regression :
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
theorem forceCollapseIndexTraced_tie_chooses_top_regression :
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
theorem mergeForceCollapseLoopTraced_zero_fuel_regression :
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
theorem mergeForceCollapseLoopTraced_delegated_failure_regression :
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

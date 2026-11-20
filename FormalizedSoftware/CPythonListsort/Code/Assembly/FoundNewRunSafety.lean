/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeAtSafety
import Code.Policy.FoundNewRunPreservation

/-!
# `found_new_run` safety

This module traces the pending-stack reads, the delegated `merge_at` calls,
and the final top-power write performed by `found_new_run`.  Power computation
has no indexed-memory event of its own.  Exhausting either explicit bound is
recorded in the trace, while the public theorem proves that source-admitted
executions never take either exhaustion branch.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

private def foundNewRunSuccessResult (state : MergeState κ ν) :
    FoundNewRunResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def foundNewRunOutOfFuelResult (state : MergeState κ ν) :
    FoundNewRunResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

private def foundNewRunFromMergeAt (result : MergeAtResult κ ν) :
    FoundNewRunResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Trace the single C field write which initializes the current top run's
power.  Constructing the replacement record does not add a synthetic read. -/
def setTopPowerTraced? (state : MergeState κ ν) (power : Nat) :
    TraceResult (MergeState κ ν) :=
  if state.pending.isEmpty then
    TraceResult.failure
  else
    TraceResult.pendingRunPowerWrite? state
      (Int.ofNat (state.pending.size - 1)) power

/-- Traced collapse loop used by `foundNewRunTraced?`. -/
def foundNewRunLoopTraced? :
    Nat → MergeState κ ν → Nat → TraceResult (FoundNewRunResult κ ν)
  | 0, state, _ =>
      (TraceResult.pure (foundNewRunOutOfFuelResult state)).markFuelExhausted
  | fuel + 1, state, power =>
      if 1 < state.pending.size then
        (TraceResult.pendingRunRead? state
          (Int.ofNat (state.pending.size - 2))).bind fun preceding =>
            match preceding.power with
            | none => TraceResult.failure
            | some precedingPower =>
                if power < precedingPower then
                  (mergeAtTraced? state (state.pending.size - 2)).bind fun merged =>
                    if merged.returnCode = 0 ∧ !merged.fuelExhausted then
                      foundNewRunLoopTraced? fuel merged.state power
                    else
                      TraceResult.pure (foundNewRunFromMergeAt merged)
                else
                  (setTopPowerTraced? state power).map foundNewRunSuccessResult
      else
        (setTopPowerTraced? state power).map foundNewRunSuccessResult

/-- Fully traced `found_new_run` evaluator. -/
def foundNewRunTraced? (state : MergeState κ ν) (n2 : Nat) :
    TraceResult (FoundNewRunResult κ ν) :=
  if state.pending.isEmpty then
    TraceResult.pure (foundNewRunSuccessResult state)
  else
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).bind fun top =>
        if (!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
            (0 : PySSize).slt top.len && decide (0 < n2) &&
            decide (n2 ≤ PY_SSIZE_T_MAX) &&
            decide (top.base - state.basekeys + top.len.toNat + n2 ≤
              state.listlen.toNat) then
          let powered := powerloopTraced
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            (BitVec.ofNat 64 n2) state.listlen
          if !powered.stopped then
            (TraceResult.pure
              (foundNewRunOutOfFuelResult state)).markFuelExhausted
          else
            foundNewRunLoopTraced? state.pending.size state powered.result
        else
          TraceResult.failure

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

private theorem pendingRunRead_safe (state : MergeState κ ν) (index : Int)
    (hindex : 0 ≤ index ∧ index.toNat < state.pending.size) :
    MovementTraceSafe (TraceResult.pendingRunRead? state index) := by
  constructor
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_pendingRunRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds] using
        (show 0 ≤ index ∧ index < Int.ofNat state.pending.size from
          ⟨hindex.1, (Int.toNat_lt hindex.1).mp hindex.2⟩)
  · simp [TraceResult.trace_pendingRunRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem pendingRunPowerWrite_safe (state : MergeState κ ν)
    (index : Int) (power : Nat)
    (hindex : 0 ≤ index ∧ index.toNat < state.pending.size) :
    MovementTraceSafe
      (TraceResult.pendingRunPowerWrite? state index power) := by
  constructor
  · simp [TraceResult.trace_pendingRunPowerWrite,
      AccessTrace.singletonAccess]
  · simp [TraceResult.trace_pendingRunPowerWrite,
      AccessTrace.singletonAccess]
  · rw [TraceResult.trace_pendingRunPowerWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds] using
        (show 0 ≤ index ∧ index < Int.ofNat state.pending.size from
          ⟨hindex.1, (Int.toNat_lt hindex.1).mp hindex.2⟩)
  · simp [TraceResult.trace_pendingRunPowerWrite,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem pendingRunPowerWrite_result_of_lookup
    (state : MergeState κ ν) (index power : Nat) (top : PendingRun)
    (hlookup : state.pending[index]? = some top) :
    (TraceResult.pendingRunPowerWrite? state (Int.ofNat index) power).result =
      some
        { state with
          pending := state.pending.setIfInBounds index
            ({ top with power := some power } : PendingRun) } := by
  change
    (TraceResult.pendingRunPowerWrite? state (Int.ofNat index) power).erase = _
  rw [TraceResult.erase_pendingRunPowerWrite]
  have hnonnegative : 0 ≤ Int.ofNat index := Int.natCast_nonneg _
  rw [if_pos hnonnegative]
  have htoi : (Int.ofNat index).toNat = index := rfl
  rw [htoi]
  simp [hlookup]

private theorem pySSize_slt_zero_of_nonnegative_positive (x : PySSize)
    (hnonnegative : x.Nonnegative) (hpositive : 0 < x.toNat) :
    (0 : PySSize).slt x := by
  rw [BitVec.slt_eq_decide, decide_eq_true_eq]
  rw [BitVec.toInt_eq_toNat_of_msb hnonnegative]
  norm_num [BitVec.toInt_ofNat]
  exact_mod_cast hpositive

/-- State fields which `found_new_run` is not allowed to change. -/
structure FoundNewRunStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace FoundNewRunStableFrame

theorem refl (state : MergeState κ ν) : FoundNewRunStableFrame state state := by
  constructor <;> rfl

theorem trans {first second third : MergeState κ ν}
    (hfirst : FoundNewRunStableFrame first second)
    (hsecond : FoundNewRunStableFrame second third) :
    FoundNewRunStableFrame first third := by
  constructor
  · exact hsecond.listlen.trans hfirst.listlen
  · exact hsecond.basekeys.trans hfirst.basekeys
  · exact hsecond.dataSize.trans hfirst.dataSize
  · exact hsecond.tempValuesMode.trans hfirst.tempValuesMode
  · exact hsecond.comparator.trans hfirst.comparator
  · exact hsecond.mrCurrent.trans hfirst.mrCurrent
  · exact hsecond.mrE.trans hfirst.mrE
  · exact hsecond.mrMask.trans hfirst.mrMask

theorem of_mergeAt {before after : MergeState κ ν}
    (h : MergeAtStableFrame before after) :
    FoundNewRunStableFrame before after := by
  exact
    { listlen := h.listlen
      basekeys := h.basekeys
      dataSize := h.dataSize
      tempValuesMode := h.tempValuesMode
      comparator := h.comparator
      mrCurrent := h.mrCurrent
      mrE := h.mrE
      mrMask := h.mrMask }

end FoundNewRunStableFrame

@[simp]
theorem erase_setTopPowerTraced (state : MergeState κ ν) (power : Nat) :
    (setTopPowerTraced? state power).erase = setTopPower? state power := by
  unfold setTopPowerTraced? setTopPower?
  split
  · rfl
  · rw [TraceResult.erase_pendingRunPowerWrite]
    have hnonnegative :
        0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi :
        (Int.ofNat (state.pending.size - 1)).toNat =
          state.pending.size - 1 := rfl
    rw [htoi]
    generalize hlookup : state.pending[state.pending.size - 1]? = lookup
    cases lookup <;> simp [Option.map, hlookup]

/-- Updating the top run's power cannot manufacture a merge-memory lifecycle
event: it either performs one pending-record write or returns an empty trace. -/
private theorem setTopPowerTraced_memoryEvents_eq_nil
    (state : MergeState κ ν) (power : Nat) :
    (setTopPowerTraced? state power).trace.memoryEvents = [] := by
  unfold setTopPowerTraced?
  split <;> simp [TraceResult.failure,
    TraceResult.trace_pendingRunPowerWrite, AccessTrace.singletonAccess,
    AccessTrace.empty]

private structure SetTopPowerSafetyPost (before : MergeState κ ν)
    (power : Nat) (after : MergeState κ ν) : Prop where
  resultEq : (setTopPowerTraced? before power).result = some after
  traceSafe : MovementTraceSafe (setTopPowerTraced? before power)
  exactErasure : (setTopPowerTraced? before power).erase =
    setTopPower? before power
  stableFrame : FoundNewRunStableFrame before after
  storageEq : after.a = before.a
  allocedEq : after.alloced = before.alloced
  dataEq : after.data = before.data
  pendingSize : after.pending.size = before.pending.size

private theorem setTopPowerTraced_safe (state : MergeState κ ν)
    (power : Nat) (hnonempty : state.pending.toList ≠ []) :
    ∃ after, SetTopPowerSafetyPost state power after := by
  have hsizePositive : 0 < state.pending.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hnonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using hzero
  let index := state.pending.size - 1
  have hindex : index < state.pending.size := by
    dsimp [index]
    omega
  let top := state.pending[index]
  have hlookup : state.pending[index]? = some top := by
    exact Array.getElem?_eq_getElem hindex
  let after : MergeState κ ν :=
    { state with
      pending := state.pending.setIfInBounds index
        ({ top with power := some power } : PendingRun) }
  have hwriteResult :
      (TraceResult.pendingRunPowerWrite? state (Int.ofNat index) power).result =
        some after := by
    simpa [after] using
      pendingRunPowerWrite_result_of_lookup state index power top hlookup
  have hwriteSafe : MovementTraceSafe
      (TraceResult.pendingRunPowerWrite? state (Int.ofNat index) power) :=
    pendingRunPowerWrite_safe state (Int.ofNat index) power
      ⟨Int.natCast_nonneg _, by simpa using hindex⟩
  refine ⟨after, ?_⟩
  constructor
  · unfold setTopPowerTraced?
    rw [if_neg]
    · exact hwriteResult
    · simpa [Array.isEmpty_iff_size_eq_zero] using ne_of_gt hsizePositive
  · unfold setTopPowerTraced?
    rw [if_neg]
    · exact hwriteSafe
    · simpa [Array.isEmpty_iff_size_eq_zero] using ne_of_gt hsizePositive
  · exact erase_setTopPowerTraced state power
  · constructor <;> rfl
  · rfl
  · rfl
  · rfl
  · simp [after]

private theorem newRun_not_mem_of_layout
    {state : MergeState κ ν} {scanned : Nat} {newRun : PendingRun}
    (hlayout : PendingLayout state scanned)
    (hnewBase : newRun.base = state.basekeys + scanned) :
    newRun ∉ state.pending.toList := by
  intro hmember
  have hspec := hlayout.2.2.2.member_spec hmember
  have hbaseLt : newRun.base < state.basekeys + scanned := by
    simp only [PendingRun.endIndex] at hspec
    omega
  rw [hnewBase] at hbaseLt
  omega

private structure FoundNewRunLoopSafetyPost
    (pre : MergeState κ ν) (scanned fuel power : Nat)
    (result : FoundNewRunResult κ ν) : Prop where
  resultEq : (foundNewRunLoopTraced? fuel pre power).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe (foundNewRunLoopTraced? fuel pre power)
  exactErasure : (foundNewRunLoopTraced? fuel pre power).erase =
    foundNewRunLoop? fuel pre power
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  stableFrame : FoundNewRunStableFrame pre result.state
  memoryEventsValid :
    (foundNewRunLoopTraced? fuel pre power).trace.memoryEventsValid
      pre.a.hasValues
  onlyMergeMemoryEvents :
    (foundNewRunLoopTraced? fuel pre power).trace.onlyMergeMemoryEvents
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (foundNewRunLoopTraced? fuel pre power).trace.mergeMemoryEventsBounded
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound
  memorySegment :
    (foundNewRunLoopTraced? fuel pre power).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState pre)
      (MergeMemorySnapshot.ofState result.state)

private theorem foundNewRunLoopTraced_safe
    (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
    (before : List PendingRun) (top newRun : PendingRun) (power : Nat)
    (hfuel : fuel = state.pending.size)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hpowered : PoweredPrefix state)
    (hsplit : state.pending.toList = before ++ [top])
    (hnewBase : newRun.base = state.basekeys + scanned)
    (hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (hpower : power =
      pendingBoundaryPower state.basekeys state.listlen top newRun)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result, FoundNewRunLoopSafetyPost state scanned fuel power result := by
  induction fuel generalizing state before top with
  | zero =>
      have hsizePositive : 0 < state.pending.size := by
        have hlength := congrArg List.length hsplit
        simp only [Array.length_toList, List.length_append,
          List.length_singleton] at hlength
        omega
      omega
  | succ remaining ih =>
      have hsize : state.pending.size = before.length + 1 := by
        have hlength := congrArg List.length hsplit
        simpa using hlength
      by_cases hmany : 1 < state.pending.size
      · rcases List.eq_nil_or_concat' before with hbeforeEmpty |
          ⟨older, preceding, hbefore⟩
        · subst before
          simp at hsize
          omega
        · have hindex : state.pending.size - 2 < state.pending.size := by
            omega
          have hlookup :
              state.pending[state.pending.size - 2]? = some preceding := by
            rw [← Array.getElem?_toList, hsplit, hbefore, hsize]
            simp [hbefore]
          have hreadResult :
              (TraceResult.pendingRunRead? state
                (Int.ofNat (state.pending.size - 2))).result =
                  some preceding := by
            have hget : state.pending[state.pending.size - 2] = preceding := by
              rw [Array.getElem?_eq_getElem hindex] at hlookup
              exact Option.some.inj hlookup
            rw [pendingRunRead_result_of_bounds state
              (state.pending.size - 2) hindex, hget]
          have hreadSafe : MovementTraceSafe
              (TraceResult.pendingRunRead? state
                (Int.ofNat (state.pending.size - 2))) :=
            pendingRunRead_safe state _
              ⟨Int.natCast_nonneg _, by simpa using hindex⟩
          have hprecedingPower : preceding.power = some
              (pendingBoundaryPower state.basekeys state.listlen
                preceding top) := by
            apply hpowered.boundary_power (before := older) (after := [])
            simpa [hbefore, List.append_assoc] using hsplit
          let precedingPower :=
            pendingBoundaryPower state.basekeys state.listlen preceding top
          by_cases hguard : power < precedingPower
          · rcases mergeAt_safe state scanned (state.pending.size - 2)
                hlayout hmax (Or.inl (by omega)) hInv hLive hMode with
              ⟨merged, hmerge⟩
            have hmergeSafe : MovementTraceSafe
                (mergeAtTraced? state (state.pending.size - 2)) :=
              ⟨hmerge.traceFuel, hmerge.noPushes, hmerge.accessesInBounds,
                hmerge.tempAccessesLive⟩
            have hmergeRaw :
                mergeAt? state (state.pending.size - 2) = some merged := by
              rw [← hmerge.exactErasure]
              exact hmerge.resultEq
            have hmergeSuccess :
                merged.returnCode = 0 ∧ !merged.fuelExhausted := by
              exact ⟨hmerge.returnCode, by simp [hmerge.resultFuel]⟩
            have houtside : newRun ∉ state.pending.toList :=
              newRun_not_mem_of_layout hlayout hnewBase
            have hpolicy := mergeTop_preserves_poweredPrefix
              state scanned older preceding top newRun precedingPower power
              merged hmax hlayout hpowered
              (by simpa [hbefore, List.append_assoc] using hsplit)
              hnewBase hnewNonnegative hnewPositive hnewWithin houtside
              (by simpa [precedingPower] using hprecedingPower) rfl hpower
              hguard hmergeRaw hmerge.returnCode hmerge.resultFuel
            let mergedTop : PendingRun :=
              { preceding with len := preceding.len + top.len }
            have hmergedSplit : merged.state.pending.toList =
                older ++ [mergedTop] := by
              simpa [mergedTop] using hpolicy.1
            have hmergedPowered : PoweredPrefix merged.state :=
              hpolicy.2.2.2.1
            have hmergedPower : power = pendingBoundaryPower
                merged.state.basekeys merged.state.listlen mergedTop newRun := by
              simpa [mergedTop] using hpolicy.2.2.2.2
            have hremaining : remaining = merged.state.pending.size := by
              have hmergedLength := congrArg List.length hmergedSplit
              simp only [Array.length_toList, List.length_append,
                List.length_singleton] at hmergedLength
              rw [hbefore] at hsize
              simp only [List.length_append, List.length_singleton] at hsize
              omega
            have hmergedMax :
                merged.state.listlen.toNat ≤ PY_LIST_MAX := by
              rw [hmerge.stableFrame.listlen]
              exact hmax
            have hmergedNewBase :
                newRun.base = merged.state.basekeys + scanned := by
              rw [hmerge.stableFrame.basekeys]
              exact hnewBase
            have hmergedNewWithin :
                scanned + newRun.len.toNat ≤ merged.state.listlen.toNat := by
              rw [hmerge.stableFrame.listlen]
              exact hnewWithin
            rcases ih merged.state older mergedTop hremaining hmergedMax
                hmerge.pendingLayout hmergedPowered hmergedSplit
                hmergedNewBase hmergedNewWithin hmergedPower
                hmerge.tempInvariant hmerge.tempLive hmerge.valuesMode with
              ⟨result, hresult⟩
            have hmemoryEvents :
                (foundNewRunLoopTraced? (remaining + 1) state power).trace.memoryEvents =
                  (mergeAtTraced? state (state.pending.size - 2)).trace.memoryEvents ++
                    (foundNewRunLoopTraced? remaining merged.state power).trace.memoryEvents := by
              simp only [foundNewRunLoopTraced?, hmany, if_pos,
                TraceResult.trace_bind, hreadResult]
              simp only [hprecedingPower]
              rw [if_pos (by simpa [precedingPower] using hguard)]
              simp only [TraceResult.trace_bind, hmerge.resultEq]
              rw [if_pos hmergeSuccess]
              simp [AccessTrace.memoryEvents_compose,
                TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
            refine ⟨result, ?_⟩
            constructor
            · simp only [foundNewRunLoopTraced?, hmany, if_pos]
              rw [TraceResult.bind_result_of_eq_some _ _ preceding hreadResult]
              simp only [hprecedingPower]
              rw [if_pos (by simpa [precedingPower] using hguard)]
              rw [TraceResult.bind_result_of_eq_some _ _ merged
                hmerge.resultEq]
              rw [if_pos hmergeSuccess]
              exact hresult.resultEq
            · exact hresult.returnCode
            · exact hresult.resultFuel
            · simp only [foundNewRunLoopTraced?, hmany, if_pos]
              apply MovementTraceSafe.bind _ _ preceding hreadResult hreadSafe
              simp only [hprecedingPower]
              rw [if_pos (by simpa [precedingPower] using hguard)]
              apply MovementTraceSafe.bind _ _ merged hmerge.resultEq
                hmergeSafe
              rw [if_pos hmergeSuccess]
              exact hresult.traceSafe
            · simp only [foundNewRunLoopTraced?, foundNewRunLoop?, hmany,
                if_pos, TraceResult.erase_bind,
                TraceResult.erase_pendingRunRead]
              have hnonnegative :
                  0 ≤ Int.ofNat (state.pending.size - 2) :=
                Int.natCast_nonneg _
              rw [if_pos hnonnegative]
              have htoi :
                  (Int.ofNat (state.pending.size - 2)).toNat =
                    state.pending.size - 2 := rfl
              rw [htoi, hlookup]
              simp only [Option.bind_some]
              rw [hprecedingPower]
              simp only
              have hguard' : power < pendingBoundaryPower state.basekeys
                  state.listlen preceding top := by
                exact hguard
              simp only [if_pos hguard', TraceResult.erase_bind]
              rw [hmerge.exactErasure, hmergeRaw]
              simp only [Option.bind_some, if_pos hmergeSuccess]
              exact hresult.exactErasure
            · exact hresult.tempInvariant
            · exact hresult.tempLive
            · exact hresult.valuesMode
            · exact hresult.hasValuesFrame.trans hmerge.hasValuesFrame
            · exact (FoundNewRunStableFrame.of_mergeAt hmerge.stableFrame).trans
                hresult.stableFrame
            · intro event hevent
              rw [hmemoryEvents] at hevent
              rcases List.mem_append.mp hevent with hcall | hrest
              · exact hmerge.memoryEventsValid event hcall
              · have hvalid := hresult.memoryEventsValid event hrest
                rw [hmerge.hasValuesFrame] at hvalid
                exact hvalid
            · intro event hevent
              rw [hmemoryEvents] at hevent
              rcases List.mem_append.mp hevent with hcall | hrest
              · exact hmerge.onlyMergeMemoryEvents event hcall
              · exact hresult.onlyMergeMemoryEvents event hrest
            · intro hbound event hevent
              rw [hmemoryEvents] at hevent
              rcases List.mem_append.mp hevent with hcall | hrest
              · exact hmerge.memoryEventsBounded hbound event hcall
              · exact hresult.memoryEventsBounded
                    (hmerge.physicalSlotsBound hbound) event hrest
            · intro hbound
              exact hresult.physicalSlotsBound
                (hmerge.physicalSlotsBound hbound)
            · rcases hmerge.memorySegment with
                ⟨mergeCalls, hmergeEvents, hmergeChain⟩
              rcases hresult.memorySegment with
                ⟨restCalls, hrestEvents, hrestChain⟩
              refine ⟨mergeCalls ++ restCalls, ?_,
                AccessTrace.MergeMemoryCallChain.append hmergeChain hrestChain⟩
              rw [hmemoryEvents, hmergeEvents, hrestEvents]
              simp [List.map_append]
          · rcases setTopPowerTraced_safe state power
                (by simp [hsplit]) with ⟨after, hset⟩
            let result := foundNewRunSuccessResult after
            have hsetRaw : setTopPower? state power = some after := by
              rw [← hset.exactErasure]
              exact hset.resultEq
            have hmemoryEvents :
                (foundNewRunLoopTraced? (remaining + 1) state power).trace.memoryEvents = [] := by
              simp only [foundNewRunLoopTraced?, hmany, if_pos,
                TraceResult.trace_bind, hreadResult]
              simp only [hprecedingPower]
              rw [if_neg (by simpa [precedingPower] using hguard)]
              simp [TraceResult.memoryEvents_map,
                AccessTrace.memoryEvents_compose,
                TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess,
                setTopPowerTraced_memoryEvents_eq_nil]
            refine ⟨result, ?_⟩
            constructor
            · simp only [foundNewRunLoopTraced?, hmany, if_pos]
              rw [TraceResult.bind_result_of_eq_some _ _ preceding hreadResult]
              simp only [hprecedingPower]
              rw [if_neg (by simpa [precedingPower] using hguard)]
              change Option.map foundNewRunSuccessResult
                (setTopPowerTraced? state power).result = some result
              rw [hset.resultEq]
              rfl
            · rfl
            · rfl
            · simp only [foundNewRunLoopTraced?, hmany, if_pos]
              apply MovementTraceSafe.bind _ _ preceding hreadResult hreadSafe
              simp only [hprecedingPower]
              rw [if_neg (by simpa [precedingPower] using hguard)]
              exact MovementTraceSafe.map _ _ hset.traceSafe
            · simp only [foundNewRunLoopTraced?, foundNewRunLoop?, hmany,
                if_pos, TraceResult.erase_bind,
                TraceResult.erase_pendingRunRead]
              have hnonnegative :
                  0 ≤ Int.ofNat (state.pending.size - 2) :=
                Int.natCast_nonneg _
              rw [if_pos hnonnegative]
              have htoi :
                  (Int.ofNat (state.pending.size - 2)).toNat =
                    state.pending.size - 2 := rfl
              rw [htoi, hlookup]
              simp only [Option.bind_some]
              rw [hprecedingPower]
              simp only
              have hguard' : ¬power < pendingBoundaryPower state.basekeys
                  state.listlen preceding top := by
                exact hguard
              simp only [if_neg hguard', TraceResult.erase_map]
              rw [hset.exactErasure, hsetRaw]
              simp [foundNewRunSuccessResult]
            · change TempStorageInv after.a after.alloced
              rw [hset.storageEq, hset.allocedEq]
              exact hInv
            · change after.a.Live
              rw [hset.storageEq]
              exact hLive
            · change SortSlice.ValuesModeInvariant after.a.hasValues after.data
              rw [hset.storageEq, hset.dataEq]
              exact hMode
            · change after.a.hasValues = state.a.hasValues
              exact congrArg TempStorage.hasValues hset.storageEq
            · change FoundNewRunStableFrame state after
              exact hset.stableFrame
            · simp [AccessTrace.memoryEventsValid, hmemoryEvents]
            · simp [AccessTrace.onlyMergeMemoryEvents, hmemoryEvents]
            · intro _
              simp [AccessTrace.mergeMemoryEventsBounded, hmemoryEvents]
            · intro hbound
              change (MergeMemorySnapshot.ofState after).PhysicalBound
              simpa [MergeMemorySnapshot.PhysicalBound,
                MergeMemorySnapshot.ofState, hset.storageEq] using hbound
            · refine ⟨[], hmemoryEvents, ?_⟩
              rw [AccessTrace.MergeMemoryCallChain.nil_iff]
              simp [result, foundNewRunSuccessResult,
                MergeMemorySnapshot.ofState, hset.storageEq,
                hset.allocedEq, hset.dataEq]
      · rcases setTopPowerTraced_safe state power
            (by simp [hsplit]) with ⟨after, hset⟩
        let result := foundNewRunSuccessResult after
        have hsetRaw : setTopPower? state power = some after := by
          rw [← hset.exactErasure]
          exact hset.resultEq
        have hmemoryEvents :
            (foundNewRunLoopTraced? (remaining + 1) state power).trace.memoryEvents = [] := by
          simp only [foundNewRunLoopTraced?, hmany, if_false,
            TraceResult.memoryEvents_map]
          exact setTopPowerTraced_memoryEvents_eq_nil state power
        refine ⟨result, ?_⟩
        constructor
        · simp only [foundNewRunLoopTraced?, hmany, if_false]
          change Option.map foundNewRunSuccessResult
            (setTopPowerTraced? state power).result = some result
          rw [hset.resultEq]
          rfl
        · rfl
        · rfl
        · simp only [foundNewRunLoopTraced?, hmany, if_false]
          exact MovementTraceSafe.map _ _ hset.traceSafe
        · simp only [foundNewRunLoopTraced?, foundNewRunLoop?, hmany,
            if_false, TraceResult.erase_map]
          simp [hset.exactErasure, hsetRaw, foundNewRunSuccessResult]
        · change TempStorageInv after.a after.alloced
          rw [hset.storageEq, hset.allocedEq]
          exact hInv
        · change after.a.Live
          rw [hset.storageEq]
          exact hLive
        · change SortSlice.ValuesModeInvariant after.a.hasValues after.data
          rw [hset.storageEq, hset.dataEq]
          exact hMode
        · change after.a.hasValues = state.a.hasValues
          exact congrArg TempStorage.hasValues hset.storageEq
        · change FoundNewRunStableFrame state after
          exact hset.stableFrame
        · simp [AccessTrace.memoryEventsValid, hmemoryEvents]
        · simp [AccessTrace.onlyMergeMemoryEvents, hmemoryEvents]
        · intro _
          simp [AccessTrace.mergeMemoryEventsBounded, hmemoryEvents]
        · intro hbound
          change (MergeMemorySnapshot.ofState after).PhysicalBound
          simpa [MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState, hset.storageEq] using hbound
        · refine ⟨[], hmemoryEvents, ?_⟩
          rw [AccessTrace.MergeMemoryCallChain.nil_iff]
          simp [result, foundNewRunSuccessResult,
            MergeMemorySnapshot.ofState, hset.storageEq,
            hset.allocedEq, hset.dataEq]

/-- End-to-end safety certificate for one admitted `found_new_run` call. -/
structure FoundNewRunSafetyPost (pre : MergeState κ ν) (scanned : Nat)
    (newRun : PendingRun) (result : FoundNewRunResult κ ν) : Prop where
  resultEq :
    (foundNewRunTraced? pre newRun.len.toNat).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (foundNewRunTraced? pre newRun.len.toNat).trace.fuelExhausted = false
  accessesInBounds :
    (foundNewRunTraced? pre newRun.len.toNat).trace.allAccessesInBounds
  tempAccessesLive :
    (foundNewRunTraced? pre newRun.len.toNat).trace.tempPayloadAccessesLive
  noPushes :
    (foundNewRunTraced? pre newRun.len.toNat).trace.pushDepths = []
  exactErasure :
    (foundNewRunTraced? pre newRun.len.toNat).erase =
      foundNewRun? pre newRun.len.toNat
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  stableFrame : FoundNewRunStableFrame pre result.state
  memoryEventsValid :
    (foundNewRunTraced? pre newRun.len.toNat).trace.memoryEventsValid
      pre.a.hasValues
  onlyMergeMemoryEvents :
    (foundNewRunTraced? pre newRun.len.toNat).trace.onlyMergeMemoryEvents
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (foundNewRunTraced? pre newRun.len.toNat).trace.mergeMemoryEventsBounded
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound
  memorySegment :
    (foundNewRunTraced? pre newRun.len.toNat).trace.MergeMemorySegment
      (MergeMemorySnapshot.ofState pre)
      (MergeMemorySnapshot.ofState result.state)
  readyToPush : ReadyToPush result.state scanned newRun

private theorem foundNewRun_safe_core
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hpowered : PoweredPrefix state)
    (hnewBase : newRun.base = state.basekeys + scanned)
    (hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result, FoundNewRunSafetyPost state scanned newRun result := by
  by_cases hempty : state.pending.isEmpty = true
  · let result := foundNewRunSuccessResult state
    have hresult :
        (foundNewRunTraced? state newRun.len.toNat).result = some result := by
      unfold foundNewRunTraced?
      rw [if_pos hempty]
      rfl
    have hexact :
        (foundNewRunTraced? state newRun.len.toNat).erase =
          foundNewRun? state newRun.len.toNat := by
      simp [foundNewRunTraced?, foundNewRun?, hempty,
        foundNewRunSuccessResult]
    have hraw : foundNewRun? state newRun.len.toNat = some result := by
      rw [← hexact]
      exact hresult
    have houtside : newRun ∉ state.pending.toList :=
      newRun_not_mem_of_layout hlayout hnewBase
    have hready := foundNewRun_preserves_readyToPush state scanned newRun
      result hmax hlayout hpowered hnewBase hnewNonnegative hnewPositive
      hnewWithin houtside hraw rfl rfl
    have hpure : MovementTraceSafe
        (TraceResult.pure (foundNewRunSuccessResult state)) :=
      MovementTraceSafe.pure _
    have hmemoryEvents :
        (foundNewRunTraced? state newRun.len.toNat).trace.memoryEvents = [] := by
      simp [foundNewRunTraced?, hempty, TraceResult.pure,
        AccessTrace.empty]
    refine ⟨result, ?_⟩
    exact
      { resultEq := hresult
        returnCode := rfl
        resultFuel := rfl
        traceFuel := by
          simpa only [foundNewRunTraced?, if_pos hempty] using hpure.fuel
        accessesInBounds := by
          simpa only [foundNewRunTraced?, if_pos hempty] using hpure.bounds
        tempAccessesLive := by
          simpa only [foundNewRunTraced?, if_pos hempty] using hpure.tempLive
        noPushes := by
          simpa only [foundNewRunTraced?, if_pos hempty] using hpure.noPushes
        exactErasure := hexact
        tempInvariant := hInv
        tempLive := hLive
        valuesMode := hMode
        hasValuesFrame := rfl
        stableFrame := FoundNewRunStableFrame.refl state
        memoryEventsValid := by
          simp [AccessTrace.memoryEventsValid, hmemoryEvents]
        onlyMergeMemoryEvents := by
          simp [AccessTrace.onlyMergeMemoryEvents, hmemoryEvents]
        memoryEventsBounded := by
          intro _
          simp [AccessTrace.mergeMemoryEventsBounded, hmemoryEvents]
        physicalSlotsBound := by
          intro hbound
          exact hbound
        memorySegment := by
          refine ⟨[], hmemoryEvents, ?_⟩
          rw [AccessTrace.MergeMemoryCallChain.nil_iff]
          simp [result, foundNewRunSuccessResult]
        readyToPush := hready }
  · have hnonempty : state.pending.toList ≠ [] := by
      intro hpending
      apply hempty
      rw [Array.isEmpty_iff_size_eq_zero]
      have hlength := congrArg List.length hpending
      simpa using hlength
    rcases List.eq_nil_or_concat' state.pending.toList with hpending |
        ⟨before, top, hsplit⟩
    · exact (hnonempty hpending).elim
    · have hsize : state.pending.size = before.length + 1 := by
        have hlength := congrArg List.length hsplit
        simpa using hlength
      have htopIndex : state.pending.size - 1 < state.pending.size := by
        omega
      have htopLookup :
          state.pending[state.pending.size - 1]? = some top := by
        rw [← Array.getElem?_toList, hsplit, hsize]
        simp
      have htopRead :
          (TraceResult.pendingRunRead? state
            (Int.ofNat (state.pending.size - 1))).result = some top := by
        have hget : state.pending[state.pending.size - 1] = top := by
          rw [Array.getElem?_eq_getElem htopIndex] at htopLookup
          exact Option.some.inj htopLookup
        rw [pendingRunRead_result_of_bounds state
          (state.pending.size - 1) htopIndex, hget]
      have htopReadSafe : MovementTraceSafe
          (TraceResult.pendingRunRead? state
            (Int.ofNat (state.pending.size - 1))) :=
        pendingRunRead_safe state _
          ⟨Int.natCast_nonneg _, by simpa using htopIndex⟩
      have hcover : PendingRunsCover state.basekeys
          (state.basekeys + scanned) (before ++ [top]) := by
        simpa [hsplit] using hlayout.2.2.2
      have htopSpec := hcover.member_spec (run := top) (by simp)
      have htopEnd : top.endIndex = state.basekeys + scanned :=
        PendingRunsCover.last_end_eq hcover
      have hfits : top.base - state.basekeys + top.len.toNat +
          newRun.len.toNat ≤ state.listlen.toNat := by
        simp only [PendingRun.endIndex] at htopEnd
        omega
      have hnewMax : newRun.len.toNat ≤ PY_SSIZE_T_MAX := by
        have : newRun.len.toNat ≤ PY_LIST_MAX := by omega
        norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at this ⊢
        omega
      have htopSlt : (0 : PySSize).slt top.len :=
        pySSize_slt_zero_of_nonnegative_positive top.len
          htopSpec.2.1 htopSpec.2.2.1
      have hguard :
          ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
            (0 : PySSize).slt top.len && decide (0 < newRun.len.toNat) &&
            decide (newRun.len.toNat ≤ PY_SSIZE_T_MAX) &&
            decide (top.base - state.basekeys + top.len.toNat +
              newRun.len.toNat ≤ state.listlen.toNat)) = true := by
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        exact ⟨⟨⟨⟨⟨hlayout.1, htopSpec.1⟩, htopSlt⟩,
          hnewPositive⟩, hnewMax⟩, hfits⟩
      have hvalidNat := validPowerloopInput_ofNat
        (s := top.base - state.basekeys) (u := top.len.toNat)
        (v := newRun.len.toNat) (n := state.listlen.toNat)
        htopSpec.2.2.1 hnewPositive hfits hmax
      have htopLen : BitVec.ofNat 64 top.len.toNat = top.len := by simp
      have hnewLen : BitVec.ofNat 64 newRun.len.toNat = newRun.len := by simp
      have hlistlen :
          BitVec.ofNat 64 state.listlen.toNat = state.listlen := by simp
      have hvalid : ValidPowerloopInput
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len newRun.len
          state.listlen := by
        simpa [htopLen, hnewLen, hlistlen] using hvalidNat
      let powered := powerloopTraced
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
        (BitVec.ofNat 64 newRun.len.toNat) state.listlen
      have hstopped : powered.stopped = true := by
        simpa [powered, hnewLen] using
          (powerloopTraceSafety
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            newRun.len state.listlen hvalid).2
      have hpower : powered.result = pendingBoundaryPower state.basekeys
          state.listlen top newRun := by
        dsimp [powered, pendingBoundaryPower, powerloop]
        rw [hnewLen]
      rcases foundNewRunLoopTraced_safe state.pending.size state scanned
          before top newRun powered.result rfl hmax hlayout hpowered hsplit
          hnewBase hnewNonnegative hnewPositive hnewWithin hpower hInv hLive
          hMode with ⟨result, hloop⟩
      have hresult :
          (foundNewRunTraced? state newRun.len.toNat).result = some result := by
        unfold foundNewRunTraced?
        rw [if_neg hempty]
        rw [TraceResult.bind_result_of_eq_some _ _ top htopRead]
        rw [if_pos hguard]
        simp only [powered, hstopped, Bool.not_true, Bool.false_eq_true,
          if_false]
        exact hloop.resultEq
      have htraceSafe :
          MovementTraceSafe (foundNewRunTraced? state newRun.len.toNat) := by
        unfold foundNewRunTraced?
        rw [if_neg hempty]
        apply MovementTraceSafe.bind _ _ top htopRead htopReadSafe
        rw [if_pos hguard]
        simp only [powered, hstopped, Bool.not_true, Bool.false_eq_true,
          if_false]
        exact hloop.traceSafe
      have hmemoryEvents :
          (foundNewRunTraced? state newRun.len.toNat).trace.memoryEvents =
            (foundNewRunLoopTraced? state.pending.size state
              powered.result).trace.memoryEvents := by
        unfold foundNewRunTraced?
        rw [if_neg hempty]
        simp only [TraceResult.trace_bind, htopRead]
        rw [if_pos hguard]
        simp only [powered, hstopped, Bool.not_true, Bool.false_eq_true,
          if_false, AccessTrace.memoryEvents_compose,
          TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess,
          List.nil_append]
      have hexact :
          (foundNewRunTraced? state newRun.len.toNat).erase =
            foundNewRun? state newRun.len.toNat := by
        unfold foundNewRunTraced? foundNewRun?
        simp only [if_neg hempty, TraceResult.erase_bind,
          TraceResult.erase_pendingRunRead]
        have hnonnegative :
            0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
        rw [if_pos hnonnegative]
        have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
            state.pending.size - 1 := rfl
        rw [htoi, htopLookup]
        simp only [Option.bind_some, if_pos hguard, powered, hstopped,
          Bool.not_true, Bool.false_eq_true, if_false]
        exact hloop.exactErasure
      have hraw : foundNewRun? state newRun.len.toNat = some result := by
        rw [← hexact]
        exact hresult
      have houtside : newRun ∉ state.pending.toList :=
        newRun_not_mem_of_layout hlayout hnewBase
      have hready := foundNewRun_preserves_readyToPush state scanned newRun
        result hmax hlayout hpowered hnewBase hnewNonnegative hnewPositive
        hnewWithin houtside hraw hloop.returnCode hloop.resultFuel
      refine ⟨result, ?_⟩
      exact
        { resultEq := hresult
          returnCode := hloop.returnCode
          resultFuel := hloop.resultFuel
          traceFuel := htraceSafe.fuel
          accessesInBounds := htraceSafe.bounds
          tempAccessesLive := htraceSafe.tempLive
          noPushes := htraceSafe.noPushes
          exactErasure := hexact
          tempInvariant := hloop.tempInvariant
          tempLive := hloop.tempLive
          valuesMode := hloop.valuesMode
          hasValuesFrame := hloop.hasValuesFrame
          stableFrame := hloop.stableFrame
          memoryEventsValid := by
            rw [AccessTrace.memoryEventsValid]
            intro event hevent
            rw [hmemoryEvents] at hevent
            exact hloop.memoryEventsValid event hevent
          onlyMergeMemoryEvents := by
            rw [AccessTrace.onlyMergeMemoryEvents]
            intro event hevent
            rw [hmemoryEvents] at hevent
            exact hloop.onlyMergeMemoryEvents event hevent
          memoryEventsBounded := by
            intro hbound
            rw [AccessTrace.mergeMemoryEventsBounded]
            intro event hevent
            rw [hmemoryEvents] at hevent
            exact hloop.memoryEventsBounded hbound event hevent
          physicalSlotsBound := hloop.physicalSlotsBound
          memorySegment := by
            rcases hloop.memorySegment with ⟨calls, hevents, hchain⟩
            exact ⟨calls, hmemoryEvents.trans hevents, hchain⟩
          readyToPush := hready }

/-- A source-admitted `found_new_run` execution exists, never exhausts either
explicit bound, performs no pending push, preserves live temporary storage,
and establishes the policy state required by the caller's push. -/
theorem foundNewRun_safe
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hpowered : PoweredPrefix state)
    (hnewBase : newRun.base = state.basekeys + scanned)
    (hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result, FoundNewRunSafetyPost state scanned newRun result :=
  foundNewRun_safe_core state scanned newRun hmax hlayout hpowered hnewBase
    hnewNonnegative hnewPositive hnewWithin hInv hLive hMode

/-- The synthetic zero-fuel branch is visibly marked in addition to returning
the transcription's fuel-exhausted result. -/
@[simp]
theorem foundNewRunLoopTraced_zero_traceFuel
    (state : MergeState κ ν) (power : Nat) :
    (foundNewRunLoopTraced? 0 state power).trace.fuelExhausted = true := by
  rfl

/-- Erasure also agrees on the independently observable loop-fuel failure. -/
@[simp]
theorem erase_foundNewRunLoopTraced_zero
    (state : MergeState κ ν) (power : Nat) :
    (foundNewRunLoopTraced? 0 state power).erase =
      foundNewRunLoop? 0 state power := by
  simp [foundNewRunLoopTraced?, foundNewRunLoop?,
    foundNewRunOutOfFuelResult]

/-- The zero-loop branch returns the matching `-1`/fuel-exhausted payload. -/
@[simp]
theorem foundNewRunLoopTraced_zero_result
    (state : MergeState κ ν) (power : Nat) :
    (foundNewRunLoopTraced? 0 state power).result.map
        (fun result => (result.returnCode, result.fuelExhausted)) =
      some (-1, true) := by
  rfl

/-- The source's empty-stack fast path performs no indexed access. -/
theorem foundNewRunTraced_empty_accesses
    (state : MergeState κ ν) (n2 : Nat)
    (hempty : state.pending.isEmpty = true) :
    (foundNewRunTraced? state n2).trace.accesses = [] := by
  unfold foundNewRunTraced?
  rw [if_pos hempty]
  rfl

/-- A successful entry to the nonempty path begins with exactly the source's
read of the current top pending record. -/
theorem foundNewRunTraced_top_read_prefix
    (state : MergeState κ ν) (n2 : Nat)
    (hsize : 0 < state.pending.size) :
    ∃ tail,
      (foundNewRunTraced? state n2).trace.accesses =
        { kind := .read
          region := .pendingRuns
          index := Int.ofNat (state.pending.size - 1)
          extent := state.pending.size } :: tail := by
  have hnotEmpty : state.pending.isEmpty ≠ true := by
    intro hempty
    rw [Array.isEmpty_iff_size_eq_zero] at hempty
    omega
  have hindex : state.pending.size - 1 < state.pending.size := by omega
  let top := state.pending[state.pending.size - 1]
  have hread :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 1))).result = some top := by
    exact pendingRunRead_result_of_bounds state _ hindex
  unfold foundNewRunTraced?
  rw [if_neg hnotEmpty, TraceResult.trace_bind, hread]
  simp only [TraceResult.trace_pendingRunRead, AccessTrace.compose,
    AccessTrace.singletonAccess, List.singleton_append, List.cons.injEq,
    true_and]
  exact ⟨_, rfl⟩

/-- On an admitted nonempty entry, the trace after the top-record read is
exactly the collapse-loop trace initialized with the current pending depth.
This pins the fuel supplied at the source loop boundary rather than leaving it
as an observation about the evaluator body. -/
theorem foundNewRunTraced_loop_entry_trace
    (state : MergeState κ ν) (n2 : Nat) (top : PendingRun)
    (hnonempty : state.pending.isEmpty ≠ true)
    (htop : state.pending[state.pending.size - 1]? = some top)
    (hguard :
      ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
        (0 : PySSize).slt top.len && decide (0 < n2) &&
        decide (n2 ≤ PY_SSIZE_T_MAX) &&
        decide (top.base - state.basekeys + top.len.toNat + n2 ≤
          state.listlen.toNat)) = true)
    (hstopped :
      (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
        (BitVec.ofNat 64 n2) state.listlen).stopped = true) :
    (foundNewRunTraced? state n2).trace =
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 1))).trace.compose
          (foundNewRunLoopTraced? state.pending.size state
            (powerloopTraced
              (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
              (BitVec.ofNat 64 n2) state.listlen).result).trace := by
  have hread :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 1))).result = some top := by
    change (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).erase = some top
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative :
        0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
        state.pending.size - 1 := rfl
    rw [htoi, htop]
  unfold foundNewRunTraced?
  rw [if_neg hnonempty, TraceResult.trace_bind, hread]
  simp only
  rw [if_pos hguard]
  simp only [hstopped, Bool.not_true, Bool.false_eq_true, if_false]

/-- Whenever the collapse loop has at least two records, its next observation
is the source's read of the second-last record. -/
theorem foundNewRunLoopTraced_secondLast_read_prefix
    (fuel : Nat) (state : MergeState κ ν) (power : Nat)
    (hmany : 1 < state.pending.size) :
    ∃ tail,
      (foundNewRunLoopTraced? (fuel + 1) state power).trace.accesses =
        { kind := .read
          region := .pendingRuns
          index := Int.ofNat (state.pending.size - 2)
          extent := state.pending.size } :: tail := by
  have hindex : state.pending.size - 2 < state.pending.size := by omega
  let preceding := state.pending[state.pending.size - 2]
  have hread :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 2))).result = some preceding := by
    exact pendingRunRead_result_of_bounds state _ hindex
  simp only [foundNewRunLoopTraced?, hmany, if_pos,
    TraceResult.trace_bind, hread, TraceResult.trace_pendingRunRead,
    AccessTrace.compose, AccessTrace.singletonAccess, List.singleton_append]
  exact ⟨_, rfl⟩

/-- On a taken merge branch, the second-last read, the complete delegated
`merge_at` trace, and the next collapse-loop trace compose in that order. -/
theorem foundNewRunLoopTraced_merge_trace_order
    (fuel : Nat) (state : MergeState κ ν) (power : Nat)
    (preceding : PendingRun) (precedingPower : Nat)
    (merged : MergeAtResult κ ν)
    (hmany : 1 < state.pending.size)
    (hlookup :
      state.pending[state.pending.size - 2]? = some preceding)
    (hprecedingPower : preceding.power = some precedingPower)
    (hguard : power < precedingPower)
    (hmerge :
      (mergeAtTraced? state (state.pending.size - 2)).result = some merged)
    (hsuccess : merged.returnCode = 0 ∧ !merged.fuelExhausted) :
    (foundNewRunLoopTraced? (fuel + 1) state power).trace =
      (AccessTrace.singletonAccess .read .pendingRuns
        (Int.ofNat (state.pending.size - 2)) state.pending.size).compose
          ((mergeAtTraced? state (state.pending.size - 2)).trace.compose
            (foundNewRunLoopTraced? fuel merged.state power).trace) := by
  have hindex : state.pending.size - 2 < state.pending.size := by omega
  have hread :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 2))).result = some preceding := by
    have hget : state.pending[state.pending.size - 2] = preceding := by
      rw [Array.getElem?_eq_getElem hindex] at hlookup
      exact Option.some.inj hlookup
    rw [pendingRunRead_result_of_bounds state
      (state.pending.size - 2) hindex, hget]
  simp only [foundNewRunLoopTraced?, hmany, if_pos,
    TraceResult.trace_bind, hread]
  rw [hprecedingPower]
  simp only
  rw [if_pos hguard, TraceResult.trace_bind, hmerge]
  simp only
  rw [if_pos hsuccess, TraceResult.trace_pendingRunRead]

/-- The arithmetic fact used by every recursive merge step: replacing a top
pair by one merged run turns predecessor fuel into the new pending depth. -/
theorem foundNewRunLoop_fuel_tracks_top_merge
    (fuel : Nat) (before : List PendingRun)
    (state after : MergeState κ ν) (left right merged : PendingRun)
    (hfuel : fuel + 1 = state.pending.size)
    (hbefore : state.pending.toList = before ++ [left, right])
    (hafter : after.pending.toList = before ++ [merged]) :
    fuel = after.pending.size := by
  have hbeforeLength := congrArg List.length hbefore
  have hafterLength := congrArg List.length hafter
  simp only [Array.length_toList, List.length_append, List.length_cons,
    List.length_nil] at hbeforeLength hafterLength
  omega

/-- The final power assignment itself emits one write and no synthetic read. -/
theorem setTopPowerTraced_singleton_write
    (state : MergeState κ ν) (power : Nat)
    (hsize : 0 < state.pending.size) :
    (setTopPowerTraced? state power).trace.accesses =
      [{ kind := .write
         region := .pendingRuns
         index := Int.ofNat (state.pending.size - 1)
         extent := state.pending.size }] := by
  have hnotEmpty : state.pending.isEmpty ≠ true := by
    intro hempty
    rw [Array.isEmpty_iff_size_eq_zero] at hempty
    omega
  unfold setTopPowerTraced?
  rw [if_neg hnotEmpty]
  simp [TraceResult.trace_pendingRunPowerWrite,
    AccessTrace.singletonAccess]

/-- With one pending run, the collapse helper performs only its final power
write.  This is the loop half of the closed read-then-write regression. -/
theorem foundNewRunLoopTraced_singleton_write
    (fuel : Nat) (state : MergeState κ ν) (power : Nat)
    (hsize : state.pending.size = 1) :
    (foundNewRunLoopTraced? (fuel + 1) state power).trace.accesses =
      [{ kind := .write
         region := .pendingRuns
         index := 0
         extent := 1 }] := by
  have hnotMany : ¬1 < state.pending.size := by omega
  simp only [foundNewRunLoopTraced?, hnotMany, if_false]
  change (setTopPowerTraced? state power).trace.accesses = _
  rw [setTopPowerTraced_singleton_write state power (by omega)]
  simp [hsize]

/-- If the fixed-width power loop itself failed to stop, the outer bound is
both marked in the trace and erased to the transcription's exhaustion return. -/
theorem foundNewRunTraced_powerloop_exhaustion
    (state : MergeState κ ν) (n2 : Nat) (top : PendingRun)
    (hnonempty : state.pending.isEmpty ≠ true)
    (htop : state.pending[state.pending.size - 1]? = some top)
    (hguard :
      ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
        (0 : PySSize).slt top.len && decide (0 < n2) &&
        decide (n2 ≤ PY_SSIZE_T_MAX) &&
        decide (top.base - state.basekeys + top.len.toNat + n2 ≤
          state.listlen.toNat)) = true)
    (hstopped :
      (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
        (BitVec.ofNat 64 n2) state.listlen).stopped = false) :
    (foundNewRunTraced? state n2).trace.fuelExhausted = true ∧
      (foundNewRunTraced? state n2).erase = foundNewRun? state n2 := by
  have hread :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 1))).result = some top := by
    change (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).erase = some top
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative :
        0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
        state.pending.size - 1 := rfl
    rw [htoi, htop]
  constructor
  · unfold foundNewRunTraced?
    rw [if_neg hnonempty, TraceResult.trace_bind, hread]
    simp only
    rw [if_pos hguard]
    simp [hstopped, TraceResult.markFuelExhausted, AccessTrace.compose,
      AccessTrace.exhausted]
  · unfold foundNewRunTraced? foundNewRun?
    simp only [if_neg hnonempty, TraceResult.erase_bind,
      TraceResult.erase_pendingRunRead]
    have hnonnegative :
        0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
        state.pending.size - 1 := rfl
    rw [htoi, htop]
    simp only [Option.bind_some, if_pos hguard, hstopped, Bool.not_false,
      if_pos, TraceResult.erase_markFuelExhausted, TraceResult.erase_pure]
    simp [foundNewRunOutOfFuelResult]

/-- For a singleton pending stack on the admitted power path, the complete
access order is exactly `read top; write top`. -/
theorem foundNewRunTraced_singleton_access_order
    (state : MergeState κ ν) (n2 : Nat) (top : PendingRun)
    (hsize : state.pending.size = 1)
    (htop : state.pending[0]? = some top)
    (hguard :
      ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
        (0 : PySSize).slt top.len && decide (0 < n2) &&
        decide (n2 ≤ PY_SSIZE_T_MAX) &&
        decide (top.base - state.basekeys + top.len.toNat + n2 ≤
          state.listlen.toNat)) = true)
    (hstopped :
      (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
        (BitVec.ofNat 64 n2) state.listlen).stopped = true) :
    (foundNewRunTraced? state n2).trace.accesses =
      [{ kind := .read, region := .pendingRuns, index := 0, extent := 1 },
       { kind := .write, region := .pendingRuns, index := 0, extent := 1 }] := by
  have hnotEmpty : state.pending.isEmpty ≠ true := by
    intro hempty
    rw [Array.isEmpty_iff_size_eq_zero] at hempty
    omega
  have htop' : state.pending[state.pending.size - 1]? = some top := by
    simpa [hsize] using htop
  have hread :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 1))).result = some top := by
    change (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).erase = some top
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative :
        0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
        state.pending.size - 1 := rfl
    rw [htoi, htop']
  have hloop := foundNewRunLoopTraced_singleton_write 0 state
    (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
      (BitVec.ofNat 64 n2) state.listlen).result hsize
  unfold foundNewRunTraced?
  rw [if_neg hnotEmpty, TraceResult.trace_bind, hread]
  simp only
  rw [if_pos hguard]
  simp only [hstopped, Bool.not_true, Bool.false_eq_true, if_false]
  rw [show state.pending.size = 0 + 1 by omega]
  change
    (TraceResult.pendingRunRead? state (Int.ofNat 0)).trace.accesses ++
      (foundNewRunLoopTraced? (0 + 1) state
        (powerloopTraced
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
          (BitVec.ofNat 64 n2) state.listlen).result).trace.accesses = _
  rw [hloop]
  simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess, hsize]

private def foundNewRunUnpoweredOlder : PendingRun :=
  { base := 0, len := 1, power := none }

private def foundNewRunUnpoweredNewest : PendingRun :=
  { base := 1, len := 1, power := none }

private def foundNewRunUnpoweredRegressionState : MergeState Nat Nat :=
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
    pending := #[foundNewRunUnpoweredOlder, foundNewRunUnpoweredNewest]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private theorem foundNewRunUnpoweredRegressionState_not_powered :
    ¬PoweredPrefix foundNewRunUnpoweredRegressionState := by
  intro hpowered
  rcases hpowered with hempty |
      ⟨olderRuns, top, hsplit, hpowers, _hexact⟩
  · simp [foundNewRunUnpoweredRegressionState] at hempty
  · have hsplit' :
        [foundNewRunUnpoweredOlder, foundNewRunUnpoweredNewest] =
          olderRuns ++ [top] := by
      simpa [foundNewRunUnpoweredRegressionState] using hsplit
    have holderRunsLength : olderRuns.length = 1 := by
      have := congrArg List.length hsplit'
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega
    obtain ⟨only, rfl⟩ := List.length_eq_one_iff.mp holderRunsLength
    simp only [List.singleton_append, List.cons.injEq] at hsplit'
    have honly := hpowers.run_power (run := only) (by simp)
    rcases honly with ⟨storedPower, hsome, _hrange⟩
    have hsomeOlder : foundNewRunUnpoweredOlder.power = some storedPower := by
      simpa [hsplit'.1] using hsome
    simp [foundNewRunUnpoweredOlder] at hsomeOlder

/-- Anti-vacuity regression for the invalid `preceding.power = none` arm.  A
concrete two-run state violates `PoweredPrefix`; the attempted second-last read
is still visible, after which the collapse evaluator returns `none` without a
fuel marker or push. -/
theorem foundNewRunLoopTraced_unpowered_preceding_failure :
    ¬PoweredPrefix foundNewRunUnpoweredRegressionState ∧
      (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).result =
        none ∧
      (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.accesses =
        [{ kind := .read
           region := .pendingRuns
           index := 0
           extent := 2 }] ∧
      (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.fuelExhausted =
        false ∧
      (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.pushDepths =
        [] := by
  refine ⟨foundNewRunUnpoweredRegressionState_not_powered, ?_⟩
  decide

/-- End-to-end form of the same anti-vacuity regression.  The outer evaluator
passes its source-domain guard, records the current-top read, enters the
collapse loop, records the uninitialized preceding run, and then fails. -/
theorem foundNewRunTraced_unpowered_prefix_failure :
    ¬PoweredPrefix foundNewRunUnpoweredRegressionState ∧
      (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).result = none ∧
      (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.accesses =
        [{ kind := .read
           region := .pendingRuns
           index := 1
           extent := 2 },
         { kind := .read
           region := .pendingRuns
           index := 0
           extent := 2 }] ∧
      (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.fuelExhausted =
        false ∧
      (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.pushDepths =
        [] := by
  refine ⟨foundNewRunUnpoweredRegressionState_not_powered, ?_⟩
  decide

end CPythonListsort

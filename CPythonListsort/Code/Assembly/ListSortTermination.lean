/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortTrace
import Code.Assembly.TopLevelErasureForceCollapse
import Code.Assembly.TopLevelErasureFound

/-!
# Top-level listsort termination and safety

This module carries the reviewed local safety certificates through the actual
traced `list_sort_impl` control flow.  The recursive proof is private; public
consumers see compact raw and proof-carrying entry-point certificates.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Trace composition -/

/-- The four whole-trace facts accumulated by the top-level induction. -/
structure ListSortTraceSafety (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  stackDepth : execution.trace.stackDepthMax ≤ 61

namespace ListSortTraceSafety

theorem pure (value : α) : ListSortTraceSafety (TraceResult.pure value) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [TraceResult.pure]
  · simp [TraceResult.pure]
  · simp [TraceResult.pure]

theorem map (execution : TraceResult α) (transform : α → β)
    (hSafe : ListSortTraceSafety execution) :
    ListSortTraceSafety (execution.map transform) := by
  exact ⟨hSafe.fuel, hSafe.accessesInBounds, hSafe.tempAccessesLive,
    hSafe.stackDepth⟩

theorem prependMemoryEvent (execution : TraceResult α)
    (event : MergeMemoryEvent) (hSafe : ListSortTraceSafety execution) :
    ListSortTraceSafety (execution.prependMemoryEvent event) := by
  exact ⟨by simpa using hSafe.fuel,
    by simpa [AccessTrace.allAccessesInBounds] using hSafe.accessesInBounds,
    by simpa [AccessTrace.tempPayloadAccessesLive] using hSafe.tempAccessesLive,
    by simpa using hSafe.stackDepth⟩

theorem appendMemoryEvent (execution : TraceResult α)
    (event : MergeMemoryEvent) (hSafe : ListSortTraceSafety execution) :
    ListSortTraceSafety (execution.appendMemoryEvent event) := by
  exact ⟨by simpa using hSafe.fuel,
    by simpa [AccessTrace.allAccessesInBounds] using hSafe.accessesInBounds,
    by simpa [AccessTrace.tempPayloadAccessesLive] using hSafe.tempAccessesLive,
    by simpa using hSafe.stackDepth⟩

theorem of_noPushes (execution : TraceResult α)
    (hFuel : execution.trace.fuelExhausted = false)
    (hBounds : execution.trace.allAccessesInBounds)
    (hLive : execution.trace.tempPayloadAccessesLive)
    (hPushes : execution.trace.pushDepths = []) :
    ListSortTraceSafety execution := by
  refine ⟨hFuel, hBounds, hLive, ?_⟩
  rw [AccessTrace.stackDepthMax, hPushes]
  simp

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (hResult : current.result = some value)
    (hCurrent : ListSortTraceSafety current)
    (hNext : ListSortTraceSafety (next value)) :
    ListSortTraceSafety (current.bind next) := by
  have htrace : (current.bind next).trace =
      current.trace.compose (next value).trace := by
    rw [TraceResult.trace_bind, hResult]
  constructor
  · rw [htrace, AccessTrace.fuelExhausted_compose_eq_false]
    exact ⟨hCurrent.fuel, hNext.fuel⟩
  · rw [htrace, AccessTrace.allAccessesInBounds_compose]
    exact ⟨hCurrent.accessesInBounds, hNext.accessesInBounds⟩
  · rw [htrace, AccessTrace.tempPayloadAccessesLive_compose]
    exact ⟨hCurrent.tempAccessesLive, hNext.tempAccessesLive⟩
  · rw [htrace, AccessTrace.stackDepthMax_compose]
    exact max_le hCurrent.stackDepth hNext.stackDepth

end ListSortTraceSafety

private theorem traceResult_bind_result_of_eq_some
    (current : TraceResult α) (next : α → TraceResult β) (value : α)
    (hResult : current.result = some value) :
    (current.bind next).result = (next value).result := by
  simp [TraceResult.bind, hResult]

private theorem mergeMemorySegment_of_events_nil
    (execution : TraceResult α) (snapshot : MergeMemorySnapshot)
    (hEvents : execution.trace.memoryEvents = []) :
    execution.trace.MergeMemorySegment snapshot snapshot := by
  exact ⟨[], by simpa using hEvents, rfl⟩

private theorem memoryEventsValid_of_events_nil
    (execution : TraceResult α) (mode : Bool)
    (hEvents : execution.trace.memoryEvents = []) :
    execution.trace.memoryEventsValid mode := by
  simp [AccessTrace.memoryEventsValid, hEvents]

private theorem mergeMemoryEventsBounded_of_events_nil
    (execution : TraceResult α)
    (hEvents : execution.trace.memoryEvents = []) :
    execution.trace.mergeMemoryEventsBounded := by
  simp [AccessTrace.mergeMemoryEventsBounded, hEvents]

/-- Operations outside the merge allocator may reorder or rewrite entries, but
the raw memory snapshot is unchanged when storage metadata is framed and both
arrays retain the same uniform keyed/unkeyed mode and extent. -/
private theorem mergeMemorySnapshot_eq_of_storage_frame
    (before after : MergeState κ ν)
    (hStorage : after.a = before.a)
    (hAlloced : after.alloced = before.alloced)
    (hSize : after.data.entries.size = before.data.entries.size)
    (hBeforeMode :
      SortSlice.ValuesModeInvariant before.a.hasValues before.data)
    (hAfterMode :
      SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
    MergeMemorySnapshot.ofState after = MergeMemorySnapshot.ofState before := by
  have hBeforeSnapshot :
      (MergeMemorySnapshot.ofState before).ValuesMode before.a.hasValues :=
    (MergeMemorySnapshot.valuesMode_ofState_iff before.a.hasValues before).2
      ⟨rfl, hBeforeMode⟩
  have hAfterSnapshot :
      (MergeMemorySnapshot.ofState after).ValuesMode before.a.hasValues :=
    (MergeMemorySnapshot.valuesMode_ofState_iff before.a.hasValues after).2
      ⟨by simpa [hStorage], by simpa [hStorage] using hAfterMode⟩
  have hMainLength :
      (MergeMemorySnapshot.ofState after).mainValuePresent.length =
        (MergeMemorySnapshot.ofState before).mainValuePresent.length := by
    simpa [MergeMemorySnapshot.ofState] using hSize
  have hMain :
      (MergeMemorySnapshot.ofState after).mainValuePresent =
        (MergeMemorySnapshot.ofState before).mainValuePresent := by
    apply List.ext_get hMainLength
    intro index hAfterIndex hBeforeIndex
    exact (hAfterSnapshot.2 index hAfterIndex).trans
      (hBeforeSnapshot.2 index hBeforeIndex).symm
  apply MergeMemorySnapshot.ext
  · exact congrArg TempStorage.backing hStorage
  · exact congrArg TempStorage.hasValues hStorage
  · exact congrArg (fun storage => storage.cells.size) hStorage
  · exact hAlloced
  · exact congrArg TempStorage.physicalSlots hStorage
  · exact hMain

/-! ## Final cleanup -/

private structure FinishListSortSuccessPost (state : MergeState κ ν)
    (reverse : Bool) (inputSize : Nat) (result : ListSortImplResult κ ν) :
    Prop where
  resultEq :
    (finishListSortTraced? state reverse inputSize 0 false).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety :
    ListSortTraceSafety
      (finishListSortTraced? state reverse inputSize 0 false)
  memoryEventsValid :
    (finishListSortTraced? state reverse inputSize 0 false).trace.memoryEventsValid
      state.a.hasValues
  memoryEventsBounded :
    (finishListSortTraced? state reverse inputSize 0 false).trace.mergeMemoryEventsBounded
  memoryTail :
    (finishListSortTraced? state reverse inputSize 0 false).trace.MergeMemoryTail
      (MergeMemorySnapshot.ofState state)
      (MergeMemorySnapshot.ofState result.state)
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = state.a.hasValues
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

private theorem finishListSortTraced_success_safe
    (state : MergeState κ ν) (reverse : Bool) (inputSize : Nat)
    (hExtent : state.data.entries.size = inputSize)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hPhysical : (MergeMemorySnapshot.ofState state).PhysicalBound)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result, FinishListSortSuccessPost state reverse inputSize result := by
  cases reverse with
  | false =>
      let result : ListSortImplResult κ ν :=
        { state := mergeFreemem state
          returnCode := 0
          fuelExhausted := false }
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp [finishListSortTraced?, TraceResult.pure, result]
          returnCode := rfl
          resultFuel := rfl
          traceSafety := by
            simpa [finishListSortTraced?, result] using
              (ListSortTraceSafety.appendMemoryEvent (TraceResult.pure result)
                (listSortCleanupMemoryEvent state)
                (ListSortTraceSafety.pure result))
          memoryEventsValid := by
            have hcleanup := MergeMemoryEvent.cleanupValid_ofState_mergeFreemem
              state.a.hasValues state hInv hLive rfl hMode
            rw [AccessTrace.memoryEventsValid]
            intro event hevent
            simp [finishListSortTraced?, TraceResult.pure,
              TraceResult.appendMemoryEvent, AccessTrace.empty,
              AccessTrace.singletonMemoryEvent] at hevent
            subst event
            simpa [MergeMemoryEvent.Valid, listSortCleanupMemoryEvent] using
              hcleanup
          memoryEventsBounded := by
            rw [AccessTrace.mergeMemoryEventsBounded]
            intro event hevent
            simp [finishListSortTraced?, TraceResult.pure,
              TraceResult.appendMemoryEvent, AccessTrace.empty,
              AccessTrace.singletonMemoryEvent] at hevent
            subst event
            trivial
          memoryTail := by
            refine ⟨[], MergeMemorySnapshot.ofState state, ?_, rfl⟩
            simp [finishListSortTraced?, TraceResult.pure,
              TraceResult.appendMemoryEvent, AccessTrace.empty,
              AccessTrace.singletonMemoryEvent, listSortCleanupMemoryEvent,
              result]
          tempInvariant := by
            simpa [result] using mergeFreemem_tempStorageInv state hInv
          valuesMode := by
            have hframe := mergeFreemem_frame state hInv
            change SortSlice.ValuesModeInvariant (mergeFreemem state).a.hasValues
              (mergeFreemem state).data
            rw [hframe.2.2.2.2.2.2.2.1, hframe.2.2.1]
            exact hMode
          hasValuesFrame := by
            have hframe := mergeFreemem_frame state hInv
            simpa [result] using hframe.2.2.2.2.2.2.2.1
          finalPhysicalBound := by
            simpa [result] using
              MergeMemoryCallEvent.physicalBound_of_mergeFreemem state hPhysical }
  | true =>
      by_cases hActive : 1 < inputSize
      · have hhi : Int.ofNat inputSize ≤
            Int.ofNat state.data.entries.size := by
          simp [hExtent]
        rcases finalReversePhase_safe state.a.hasValues state.data 0
            (Int.ofNat inputSize) (by omega) hhi
            (Int.natCast_nonneg inputSize) hMode with
          ⟨reversed, hreverse⟩
        let updated : MergeState κ ν := { state with data := reversed.slice }
        let result : ListSortImplResult κ ν :=
          { state := mergeFreemem updated
            returnCode := 0
            fuelExhausted := false }
        let cleanup : ReverseSliceResult κ ν →
            TraceResult (ListSortImplResult κ ν) := fun reversed =>
          let before : MergeState κ ν :=
            { state with data := reversed.slice }
          (TraceResult.pure
            { state := mergeFreemem before
              returnCode := 0
              fuelExhausted := false || reversed.fuelExhausted }).appendMemoryEvent
            (listSortCleanupMemoryEvent before)
        have hupdatedInv : TempStorageInv updated.a updated.alloced := by
          simpa [updated] using hInv
        have hupdatedLive : updated.a.Live := by
          simpa [updated] using hLive
        have hupdatedPhysical :
            (MergeMemorySnapshot.ofState updated).PhysicalBound := by
          simpa [updated, MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState] using hPhysical
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              unfold finishListSortTraced?
              rw [if_pos (by simp [hActive])]
              change
                ((reverseSlicePhaseTraced?
                  (finalReversePhase state.a.hasValues) state.data 0
                    (Int.ofNat inputSize)).bind cleanup).result = some result
              exact (traceResult_bind_result_of_eq_some _ _ reversed
                hreverse.resultEq).trans (by
                  simp [cleanup, updated, result, hreverse.resultFuel,
                    TraceResult.pure, TraceResult.appendMemoryEvent])
            returnCode := rfl
            resultFuel := rfl
            traceSafety := by
              have hReverseSafe : ListSortTraceSafety
                  (reverseSlicePhaseTraced? (finalReversePhase state.a.hasValues)
                    state.data 0 (Int.ofNat inputSize)) :=
                ListSortTraceSafety.of_noPushes _ hreverse.traceFuel
                  hreverse.accessesInBounds hreverse.tempAccessesLive
                  hreverse.noPushes
              have hCleanupSafe : ListSortTraceSafety
                  ((TraceResult.pure result).appendMemoryEvent
                    (listSortCleanupMemoryEvent updated)) :=
                ListSortTraceSafety.appendMemoryEvent _ _
                  (ListSortTraceSafety.pure result)
              have hBound := ListSortTraceSafety.bind
                (reverseSlicePhaseTraced?
                  (finalReversePhase state.a.hasValues) state.data 0
                    (Int.ofNat inputSize))
                cleanup
                reversed hreverse.resultEq hReverseSafe (by
                  simpa [cleanup, updated, result, hreverse.resultFuel] using
                    hCleanupSafe)
              simpa [finishListSortTraced?, hActive, cleanup] using hBound
            memoryEventsValid := by
              have hcleanup := MergeMemoryEvent.cleanupValid_ofState_mergeFreemem
                state.a.hasValues updated hupdatedInv hupdatedLive rfl
                  hreverse.valuesMode
              rw [AccessTrace.memoryEventsValid]
              intro event hevent
              have hevents := finishListSortTraced_cleanup_event_active_exact
                state true inputSize 0 false (by simp [hActive]) reversed
                  hreverse.resultEq
              rw [hevents,
                reverseSlicePhaseTraced_memoryEvents_eq_nil] at hevent
              simp only [List.nil_append, List.mem_singleton] at hevent
              subst event
              simpa [MergeMemoryEvent.Valid, listSortCleanupMemoryEvent,
                updated] using hcleanup
            memoryEventsBounded := by
              rw [AccessTrace.mergeMemoryEventsBounded]
              intro event hevent
              have hevents := finishListSortTraced_cleanup_event_active_exact
                state true inputSize 0 false (by simp [hActive]) reversed
                  hreverse.resultEq
              rw [hevents,
                reverseSlicePhaseTraced_memoryEvents_eq_nil] at hevent
              simp only [List.nil_append, List.mem_singleton] at hevent
              subst event
              trivial
            memoryTail := by
              refine ⟨[], MergeMemorySnapshot.ofState updated, ?_, ?_⟩
              · have hevents := finishListSortTraced_cleanup_event_active_exact
                  state true inputSize 0 false (by simp [hActive]) reversed
                    hreverse.resultEq
                rw [hevents, reverseSlicePhaseTraced_memoryEvents_eq_nil]
                simp [listSortCleanupMemoryEvent, updated, result]
              · exact (mergeMemorySnapshot_eq_of_storage_frame state updated
                  rfl rfl (by simpa [updated] using hreverse.sizeEq) hMode
                  (by simpa [updated] using hreverse.valuesMode)).symm
            tempInvariant := by
              simpa [result] using
                mergeFreemem_tempStorageInv updated hupdatedInv
            valuesMode := by
              have hframe := mergeFreemem_frame updated hupdatedInv
              change SortSlice.ValuesModeInvariant
                (mergeFreemem updated).a.hasValues
                (mergeFreemem updated).data
              rw [hframe.2.2.2.2.2.2.2.1, hframe.2.2.1]
              exact hreverse.valuesMode
            hasValuesFrame := by
              have hframe := mergeFreemem_frame updated hupdatedInv
              simpa [updated, result] using hframe.2.2.2.2.2.2.2.1
            finalPhysicalBound := by
              simpa [result] using
                MergeMemoryCallEvent.physicalBound_of_mergeFreemem updated
                  hupdatedPhysical }
      · let result : ListSortImplResult κ ν :=
          { state := mergeFreemem state
            returnCode := 0
            fuelExhausted := false }
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp [finishListSortTraced?, hActive, TraceResult.pure, result]
            returnCode := rfl
            resultFuel := rfl
            traceSafety := by
              simpa [finishListSortTraced?, hActive, result] using
                (ListSortTraceSafety.appendMemoryEvent (TraceResult.pure result)
                  (listSortCleanupMemoryEvent state)
                  (ListSortTraceSafety.pure result))
            memoryEventsValid := by
              have hcleanup := MergeMemoryEvent.cleanupValid_ofState_mergeFreemem
                state.a.hasValues state hInv hLive rfl hMode
              rw [AccessTrace.memoryEventsValid]
              intro event hevent
              simp [finishListSortTraced?, hActive, TraceResult.pure,
                TraceResult.appendMemoryEvent, AccessTrace.empty,
                AccessTrace.singletonMemoryEvent] at hevent
              subst event
              simpa [MergeMemoryEvent.Valid, listSortCleanupMemoryEvent] using
                hcleanup
            memoryEventsBounded := by
              rw [AccessTrace.mergeMemoryEventsBounded]
              intro event hevent
              simp [finishListSortTraced?, hActive, TraceResult.pure,
                TraceResult.appendMemoryEvent, AccessTrace.empty,
                AccessTrace.singletonMemoryEvent] at hevent
              subst event
              trivial
            memoryTail := by
              refine ⟨[], MergeMemorySnapshot.ofState state, ?_, rfl⟩
              simp [finishListSortTraced?, hActive, TraceResult.pure,
                TraceResult.appendMemoryEvent, AccessTrace.empty,
                AccessTrace.singletonMemoryEvent, listSortCleanupMemoryEvent,
                result]
            tempInvariant := by
              simpa [result] using mergeFreemem_tempStorageInv state hInv
            valuesMode := by
              have hframe := mergeFreemem_frame state hInv
              change SortSlice.ValuesModeInvariant (mergeFreemem state).a.hasValues
                (mergeFreemem state).data
              rw [hframe.2.2.2.2.2.2.2.1, hframe.2.2.1]
              exact hMode
            hasValuesFrame := by
              have hframe := mergeFreemem_frame state hInv
              simpa [result] using hframe.2.2.2.2.2.2.2.1
            finalPhysicalBound := by
              simpa [result] using
                MergeMemoryCallEvent.physicalBound_of_mergeFreemem state
                  hPhysical }

/-! ## Scan invariant and certificates -/

/-- State carried at every call of the run-discovery scan.  The adaptive
minrun generator is required only while unscanned input remains: the clipped
last target is allowed to consume the suffix and enter final collapse without
manufacturing a nonexistent next active generator state. -/
structure ListSortScanInvariant (lt : BoolComparator κ) (hasKeyfunc : Bool)
    (inputSize : Nat) (state : MergeState κ ν) (lo scanned remaining : Nat) :
    Prop where
  inputSizeLower : 2 ≤ inputSize
  inputSizeMax : inputSize ≤ PY_LIST_MAX
  listlen : state.listlen.toNat = inputSize
  listlenNonnegative : state.listlen.Nonnegative
  basekeys : state.basekeys = 0
  dataExtent : state.data.entries.size = inputSize
  cursor : lo = state.basekeys + scanned
  partition : scanned + remaining = inputSize
  pendingLayout : PendingLayout state scanned
  poweredPrefix : PoweredPrefix state
  tempInvariant : TempStorageInv state.a state.alloced
  tempLive : state.a.Live
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState state).PhysicalBound
  hasValues : state.a.hasValues = hasKeyfunc
  valuesMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data
  comparator : state.key_compare = lt
  adaptive : 0 < remaining →
    ∃ calls, AdaptiveMinrunScanInvariant state.listlen calls scanned
      state.minrunState

/-- Successful top-level scan result, including the exact raw erasure and all
trace properties accumulated from the real helper sequence. -/
structure ListSortScanSafetyPost (fuel : Nat) (state : MergeState κ ν)
    (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
    (result : ListSortImplResult κ ν) : Prop where
  resultEq :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).result =
      some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety :
    ListSortTraceSafety
      (listSortScanTraced? fuel state lo remaining reverse inputSize)
  memoryEventsValid :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).trace.memoryEventsValid
      state.a.hasValues
  memoryEventsBounded :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).trace.mergeMemoryEventsBounded
  memoryTail :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).trace.MergeMemoryTail
      (MergeMemorySnapshot.ofState state)
      (MergeMemorySnapshot.ofState result.state)
  exactErasure :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).erase =
      listSortScan? fuel state lo remaining reverse inputSize
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = state.a.hasValues
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

/-- Raw `list_sort_impl` adequacy and whole-trace safety certificate. -/
structure ListSortImplSafetyPost (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (result : ListSortImplResult κ ν) : Prop where
  resultEq :
    (listSortImplTraced? lt reverse hasKeyfunc input).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety :
    ListSortTraceSafety (listSortImplTraced? lt reverse hasKeyfunc input)
  memoryLifecycle :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.MergeMemoryLifecycle
      hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt hasKeyfunc input).1)
      (MergeMemorySnapshot.ofState result.state)
  exactErasure :
    (listSortImplTraced? lt reverse hasKeyfunc input).erase =
      listSortImpl? lt reverse hasKeyfunc input
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = hasKeyfunc
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

/-- Public proof-carrying wrapper certificate. -/
structure ListSortSafetyPost (lt : BoolComparator κ) (reverse : Bool)
    (input : ListSortInput κ ν) (result : ListSortImplResult κ ν) : Prop where
  resultEq : (listSortTraced? lt reverse input).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety : ListSortTraceSafety (listSortTraced? lt reverse input)
  memoryLifecycle :
    (listSortTraced? lt reverse input).trace.MergeMemoryLifecycle
      input.hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt input.hasKeyfunc input.slice).1)
      (MergeMemorySnapshot.ofState result.state)
  exactErasure :
    (listSortTraced? lt reverse input).erase = listSort? lt reverse input
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = input.hasKeyfunc
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

private structure ListSortExecutionPost
    (execution : TraceResult (ListSortImplResult κ ν))
    (initialHasValues : Bool) (memoryStart : MergeMemorySnapshot)
    (result : ListSortImplResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety : ListSortTraceSafety execution
  memoryEventsValid : execution.trace.memoryEventsValid initialHasValues
  memoryEventsBounded : execution.trace.mergeMemoryEventsBounded
  memoryTail : execution.trace.MergeMemoryTail memoryStart
    (MergeMemorySnapshot.ofState result.state)
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = initialHasValues
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

private theorem ListSortExecutionPost.bind_segment
    (current : TraceResult α) (next : α → TraceResult (ListSortImplResult κ ν))
    (value : α) (result : ListSortImplResult κ ν)
    (mode : Bool) (start middle : MergeMemorySnapshot)
    (hResult : current.result = some value)
    (hSafe : ListSortTraceSafety current)
    (hValid : current.trace.memoryEventsValid mode)
    (hBounded : current.trace.mergeMemoryEventsBounded)
    (hSegment : current.trace.MergeMemorySegment start middle)
    (hNext : ListSortExecutionPost (next value) mode middle result) :
    ListSortExecutionPost (current.bind next) mode start result := by
  refine
    { resultEq := (traceResult_bind_result_of_eq_some _ _ value hResult).trans
        hNext.resultEq
      returnCode := hNext.returnCode
      resultFuel := hNext.resultFuel
      traceSafety := ListSortTraceSafety.bind _ _ value hResult hSafe
        hNext.traceSafety
      memoryEventsValid := ?_
      memoryEventsBounded := ?_
      memoryTail := ?_
      finalTempInvariant := hNext.finalTempInvariant
      finalValuesMode := hNext.finalValuesMode
      finalHasValues := hNext.finalHasValues
      finalPhysicalBound := hNext.finalPhysicalBound }
  · rw [TraceResult.trace_bind, hResult,
      AccessTrace.memoryEventsValid_compose]
    exact ⟨hValid, hNext.memoryEventsValid⟩
  · rw [TraceResult.trace_bind, hResult,
      AccessTrace.mergeMemoryEventsBounded_compose]
    exact ⟨hBounded, hNext.memoryEventsBounded⟩
  · rw [TraceResult.trace_bind, hResult]
    exact AccessTrace.mergeMemoryTail_compose _ _ start middle _ hSegment
      hNext.memoryTail

private theorem ListSortExecutionPost.rebase
    (execution : TraceResult (ListSortImplResult κ ν))
    (mode : Bool) (start replacement : MergeMemorySnapshot)
    (result : ListSortImplResult κ ν)
    (hStart : start = replacement)
    (hPost : ListSortExecutionPost execution mode start result) :
    ListSortExecutionPost execution mode replacement result := by
  subst replacement
  exact hPost

private structure ListSortImplExecutionPost
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (result : ListSortImplResult κ ν) : Prop where
  resultEq :
    (listSortImplTraced? lt reverse hasKeyfunc input).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafety :
    ListSortTraceSafety (listSortImplTraced? lt reverse hasKeyfunc input)
  memoryLifecycle :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.MergeMemoryLifecycle
      hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt hasKeyfunc input).1)
      (MergeMemorySnapshot.ofState result.state)
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  finalHasValues : result.state.a.hasValues = hasKeyfunc
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound

private theorem finishListSortExecutionPost
    (state : MergeState κ ν) (reverse : Bool) (inputSize : Nat)
    (hExtent : state.data.entries.size = inputSize)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hPhysical : (MergeMemorySnapshot.ofState state).PhysicalBound)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result,
      ListSortExecutionPost
        (finishListSortTraced? state reverse inputSize 0 false)
        state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
  rcases finishListSortTraced_success_safe state reverse inputSize hExtent hInv
      hLive hPhysical hMode with ⟨result, hresult⟩
  exact ⟨result,
    { resultEq := hresult.resultEq
      returnCode := hresult.returnCode
      resultFuel := hresult.resultFuel
      traceSafety := hresult.traceSafety
      memoryEventsValid := hresult.memoryEventsValid
      memoryEventsBounded := hresult.memoryEventsBounded
      memoryTail := hresult.memoryTail
      finalTempInvariant := hresult.tempInvariant
      finalValuesMode := hresult.valuesMode
      finalHasValues := hresult.hasValuesFrame
      finalPhysicalBound := hresult.finalPhysicalBound }⟩

private theorem listSortScanTraced_terminal_safe
    (fuel : Nat) (state : MergeState κ ν) (lo scanned : Nat)
    (reverse : Bool) (inputSize : Nat) (lt : BoolComparator κ)
    (hasKeyfunc : Bool)
    (hInv : ListSortScanInvariant lt hasKeyfunc inputSize state lo scanned 0) :
    ∃ result,
      ListSortExecutionPost
        (listSortScanTraced? fuel state lo 0 reverse inputSize)
        state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
  have hScanned : 0 < scanned := by
    have hLower := hInv.inputSizeLower
    have hPartition := hInv.partition
    omega
  have hPending : state.pending.toList ≠ [] :=
    hInv.pendingLayout.pending_nonempty hScanned
  rcases mergeForceCollapse_safe state scanned
      (by simpa [hInv.listlen] using hInv.inputSizeMax) hPending
      hInv.pendingLayout hInv.tempInvariant hInv.tempLive hInv.valuesMode with
    ⟨collapsed, hcollapsed⟩
  have hCollapsedExtent : collapsed.state.data.entries.size = inputSize :=
    hcollapsed.stableFrame.dataSize.trans hInv.dataExtent
  rcases finishListSortExecutionPost collapsed.state reverse inputSize
      hCollapsedExtent hcollapsed.tempInvariant hcollapsed.tempLive
      (hcollapsed.physicalSlotsBound hInv.physicalSlotsBound)
      hcollapsed.valuesMode with
    ⟨result, hfinished⟩
  have hCollapseSafe :
      ListSortTraceSafety (mergeForceCollapseTraced? state) :=
    ListSortTraceSafety.of_noPushes _ hcollapsed.traceFuel
      hcollapsed.accessesInBounds hcollapsed.tempAccessesLive
      hcollapsed.noPushes
  have hCombined : ListSortTraceSafety
      ((mergeForceCollapseTraced? state).bind fun collapsed =>
        if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
          finishListSortTraced? collapsed.state reverse inputSize 0 false
        else
          failFromCollapseTraced? collapsed reverse inputSize) := by
    apply ListSortTraceSafety.bind _ _ collapsed hcollapsed.resultEq
      hCollapseSafe
    simpa [hcollapsed.returnCode, hcollapsed.resultFuel] using
      hfinished.traceSafety
  have hFinishedForInitial :
      ListSortExecutionPost
        (finishListSortTraced? collapsed.state reverse inputSize 0 false)
        state.a.hasValues (MergeMemorySnapshot.ofState collapsed.state)
        result := by
    simpa [hcollapsed.hasValuesFrame] using hfinished
  have hCollapsePost : ListSortExecutionPost
      ((mergeForceCollapseTraced? state).bind fun collapsed =>
        if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
          finishListSortTraced? collapsed.state reverse inputSize 0 false
        else
          failFromCollapseTraced? collapsed reverse inputSize)
      state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
    apply ListSortExecutionPost.bind_segment
      (mergeForceCollapseTraced? state)
      (fun collapsed =>
        if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
          finishListSortTraced? collapsed.state reverse inputSize 0 false
        else
          failFromCollapseTraced? collapsed reverse inputSize)
      collapsed result state.a.hasValues (MergeMemorySnapshot.ofState state)
        (MergeMemorySnapshot.ofState collapsed.state)
      hcollapsed.resultEq hCollapseSafe hcollapsed.memoryEventsValid
      (hcollapsed.memoryEventsBounded hInv.physicalSlotsBound)
      hcollapsed.memorySegment
    simpa [hcollapsed.returnCode, hcollapsed.resultFuel] using
      hFinishedForInitial
  refine ⟨result, ?_⟩
  exact
    { resultEq := by
        cases fuel <;>
          simpa [listSortScanTraced?, TraceResult.bind,
            hcollapsed.resultEq, hcollapsed.returnCode,
            hcollapsed.resultFuel] using hfinished.resultEq
      returnCode := hfinished.returnCode
      resultFuel := hfinished.resultFuel
      traceSafety := by
        cases fuel <;> simpa [listSortScanTraced?] using hCombined
      memoryEventsValid := by
        cases fuel <;> simpa [listSortScanTraced?] using
          hCollapsePost.memoryEventsValid
      memoryEventsBounded := by
        cases fuel <;> simpa [listSortScanTraced?] using
          hCollapsePost.memoryEventsBounded
      memoryTail := by
        cases fuel <;> simpa [listSortScanTraced?] using
          hCollapsePost.memoryTail
      finalTempInvariant := hfinished.finalTempInvariant
      finalValuesMode := hfinished.finalValuesMode
      finalHasValues := hfinished.finalHasValues.trans
        hcollapsed.hasValuesFrame
      finalPhysicalBound := hfinished.finalPhysicalBound }

private theorem listSortAfterExtensionTraced_safe
    (next : MergeState κ ν → Nat → Nat →
      TraceResult (ListSortImplResult κ ν))
    (state : MergeState κ ν) (lo scanned remaining runLength : Nat)
    (naturalLength target : Nat)
    (reverse : Bool) (inputSize : Nat)
    (hMax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hLayout : PendingLayout state scanned)
    (hPowered : PoweredPrefix state)
    (hBase : lo = state.basekeys + scanned)
    (hPositive : 0 < runLength)
    (hWithin : scanned + runLength ≤ state.listlen.toNat)
    (hRemaining : runLength ≤ remaining)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hPhysical : (MergeMemorySnapshot.ofState state).PhysicalBound)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hContinuation : ∀ (found : FoundNewRunResult κ ν),
      let newRun : PendingRun :=
        { base := lo, len := BitVec.ofNat 64 runLength, power := none }
      FoundNewRunSafetyPost state scanned newRun found →
        ∃ result,
          ListSortExecutionPost
            (next (pushPendingRun found.state newRun) (lo + runLength)
              (remaining - runLength))
            (pushPendingRun found.state newRun).a.hasValues
            (MergeMemorySnapshot.ofState
              (pushPendingRun found.state newRun)) result) :
    ∃ result,
      ListSortExecutionPost
        (listSortAfterExtensionTraced? next lo remaining reverse inputSize
          naturalLength target (state, runLength, false))
        state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
  let newRun : PendingRun :=
    { base := lo, len := BitVec.ofNat 64 runLength, power := none }
  have hRunMax : runLength ≤ PY_LIST_MAX := by omega
  have hRunNat : newRun.len.toNat = runLength := by
    simpa [newRun] using listSizeWord_toNat hRunMax
  have hRunNonnegative : newRun.len.Nonnegative := by
    simpa [newRun] using listSizeWord_nonnegative hRunMax
  have hNewBase : newRun.base = state.basekeys + scanned := by
    simpa [newRun] using hBase
  rcases foundNewRun_safe state scanned newRun hMax hLayout hPowered hNewBase
      hRunNonnegative (by simpa [hRunNat] using hPositive)
      (by simpa [hRunNat] using hWithin) hInv hLive hMode with
    ⟨found, hfound⟩
  rcases hContinuation found hfound with ⟨result, hnext⟩
  have hpush := pushPendingRunTraced_preserves_policy found.state scanned
    newRun hfound.readyToPush
  have hfoundEq :
      (foundNewRunTraced? state runLength).result = some found := by
    simpa [hRunNat] using hfound.resultEq
  have hValid : ¬(runLength = 0 ∨ remaining < runLength) := by
    omega
  have hFoundSafe : ListSortTraceSafety (foundNewRunTraced? state runLength) := by
    apply ListSortTraceSafety.of_noPushes
    · simpa [hRunNat] using hfound.traceFuel
    · simpa [hRunNat] using hfound.accessesInBounds
    · simpa [hRunNat] using hfound.tempAccessesLive
    · simpa [hRunNat] using hfound.noPushes
  have hPushSafe :
      ListSortTraceSafety
        (pushFormedRunTraced found.state newRun naturalLength target
          remaining) := by
    refine ⟨?_, ?_, ?_, hpush.2.2.2.1⟩
    · rfl
    · simp [pushFormedRunTraced, AccessTrace.singletonFormedRun,
        AccessTrace.allAccessesInBounds]
    · simp [pushFormedRunTraced, AccessTrace.singletonFormedRun,
        AccessTrace.tempPayloadAccessesLive]
  have hPushThen : ListSortTraceSafety
      ((pushFormedRunTraced found.state newRun naturalLength target
          remaining).bind fun pushed =>
        next pushed (lo + runLength) (remaining - runLength)) := by
    exact ListSortTraceSafety.bind _ _ (pushPendingRun found.state newRun)
      (erase_pushFormedRunTraced found.state newRun naturalLength target
        remaining) hPushSafe hnext.traceSafety
  have hPushEvents :
      (pushFormedRunTraced found.state newRun naturalLength target
        remaining).trace.memoryEvents = [] := by
    simp [pushFormedRunTraced, AccessTrace.singletonFormedRun]
  have hNextForFound :
      ListSortExecutionPost
        (next (pushPendingRun found.state newRun) (lo + runLength)
          (remaining - runLength))
        found.state.a.hasValues (MergeMemorySnapshot.ofState found.state)
        result := by
    simpa [pushPendingRun, MergeMemorySnapshot.ofState] using hnext
  have hPushPost : ListSortExecutionPost
      ((pushFormedRunTraced found.state newRun naturalLength target
          remaining).bind fun pushed =>
        next pushed (lo + runLength) (remaining - runLength))
      found.state.a.hasValues (MergeMemorySnapshot.ofState found.state)
      result := by
    exact ListSortExecutionPost.bind_segment _ _
      (pushPendingRun found.state newRun) result found.state.a.hasValues
      (MergeMemorySnapshot.ofState found.state)
      (MergeMemorySnapshot.ofState found.state)
      (erase_pushFormedRunTraced found.state newRun naturalLength target
        remaining) hPushSafe
      (memoryEventsValid_of_events_nil _ _ hPushEvents)
      (mergeMemoryEventsBounded_of_events_nil _ hPushEvents)
      (mergeMemorySegment_of_events_nil _ _ hPushEvents) hNextForFound
  have hPushPostForInitial : ListSortExecutionPost
      ((pushFormedRunTraced found.state newRun naturalLength target
          remaining).bind fun pushed =>
        next pushed (lo + runLength) (remaining - runLength))
      state.a.hasValues (MergeMemorySnapshot.ofState found.state) result := by
    simpa [hfound.hasValuesFrame] using hPushPost
  have hCombined : ListSortTraceSafety
      ((foundNewRunTraced? state runLength).bind fun found =>
        if found.returnCode = 0 ∧ !found.fuelExhausted then
          let newRun : PendingRun :=
            { base := lo, len := BitVec.ofNat 64 runLength, power := none }
          (pushFormedRunTraced found.state newRun naturalLength target
            remaining).bind fun pushed =>
            next pushed (lo + runLength) (remaining - runLength)
        else
          failFromFoundNewRunTraced? found reverse inputSize) := by
    apply ListSortTraceSafety.bind _ _ found
      hfoundEq hFoundSafe
    simpa [hfound.returnCode, hfound.resultFuel, newRun] using hPushThen
  have hFoundPost : ListSortExecutionPost
      ((foundNewRunTraced? state runLength).bind fun found =>
        if found.returnCode = 0 ∧ !found.fuelExhausted then
          let newRun : PendingRun :=
            { base := lo, len := BitVec.ofNat 64 runLength, power := none }
          (pushFormedRunTraced found.state newRun naturalLength target
            remaining).bind fun pushed =>
            next pushed (lo + runLength) (remaining - runLength)
        else
          failFromFoundNewRunTraced? found reverse inputSize)
      state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
    have hFoundValid :
        (foundNewRunTraced? state runLength).trace.memoryEventsValid
          state.a.hasValues := by
      simpa [hRunNat] using hfound.memoryEventsValid
    have hFoundBounded :
        (foundNewRunTraced? state runLength).trace.mergeMemoryEventsBounded := by
      simpa [hRunNat] using hfound.memoryEventsBounded hPhysical
    have hFoundSegment :
        (foundNewRunTraced? state runLength).trace.MergeMemorySegment
          (MergeMemorySnapshot.ofState state)
          (MergeMemorySnapshot.ofState found.state) := by
      simpa [hRunNat] using hfound.memorySegment
    apply ListSortExecutionPost.bind_segment
      (foundNewRunTraced? state runLength)
      (fun found =>
        if found.returnCode = 0 ∧ !found.fuelExhausted then
          let newRun : PendingRun :=
            { base := lo, len := BitVec.ofNat 64 runLength, power := none }
          (pushFormedRunTraced found.state newRun naturalLength target
            remaining).bind fun pushed =>
            next pushed (lo + runLength) (remaining - runLength)
        else
          failFromFoundNewRunTraced? found reverse inputSize)
      found result state.a.hasValues (MergeMemorySnapshot.ofState state)
        (MergeMemorySnapshot.ofState found.state)
      hfoundEq hFoundSafe hFoundValid hFoundBounded hFoundSegment
    simpa [hfound.returnCode, hfound.resultFuel, newRun] using
      hPushPostForInitial
  refine ⟨result, ?_⟩
  exact
    { resultEq := by
        simpa [listSortAfterExtensionTraced?, hValid] using
          hFoundPost.resultEq
      returnCode := hnext.returnCode
      resultFuel := hnext.resultFuel
      traceSafety := by
        simpa [listSortAfterExtensionTraced?, hValid]
          using hCombined
      memoryEventsValid := by
        simpa [listSortAfterExtensionTraced?, hValid] using
          hFoundPost.memoryEventsValid
      memoryEventsBounded := by
        simpa [listSortAfterExtensionTraced?, hValid] using
          hFoundPost.memoryEventsBounded
      memoryTail := by
        simpa [listSortAfterExtensionTraced?, hValid] using
          hFoundPost.memoryTail
      finalTempInvariant := hnext.finalTempInvariant
      finalValuesMode := hnext.finalValuesMode
      finalHasValues := hnext.finalHasValues.trans (by
        simpa [pushPendingRun] using hfound.hasValuesFrame)
      finalPhysicalBound := hnext.finalPhysicalBound }

theorem listSortScanInvariant_after_push
    (lt : BoolComparator κ) (hasKeyfunc : Bool) (inputSize : Nat)
    (call : MergeState κ ν) (lo scanned remaining consumed : Nat)
    (found : FoundNewRunResult κ ν)
    (hInputLower : 2 ≤ inputSize) (hInputMax : inputSize ≤ PY_LIST_MAX)
    (hListlen : call.listlen.toNat = inputSize)
    (hListNonnegative : call.listlen.Nonnegative)
    (hBasekeys : call.basekeys = 0)
    (hExtent : call.data.entries.size = inputSize)
    (hCursor : lo = call.basekeys + scanned)
    (hPartition : scanned + remaining = inputSize)
    (_hConsumedPositive : 0 < consumed)
    (hConsumedWithin : consumed ≤ remaining)
    (hPhysical : (MergeMemorySnapshot.ofState call).PhysicalBound)
    (hHasValues : call.a.hasValues = hasKeyfunc)
    (hComparator : call.key_compare = lt)
    (hAdaptiveAfter : 0 < remaining - consumed →
      ∃ calls, AdaptiveMinrunScanInvariant call.listlen calls
        (scanned + consumed) call.minrunState)
    (hFound : FoundNewRunSafetyPost call scanned
      { base := lo, len := BitVec.ofNat 64 consumed, power := none } found) :
    ListSortScanInvariant lt hasKeyfunc inputSize
      (pushPendingRun found.state
        { base := lo, len := BitVec.ofNat 64 consumed, power := none })
      (lo + consumed) (scanned + consumed) (remaining - consumed) := by
  let newRun : PendingRun :=
    { base := lo, len := BitVec.ofNat 64 consumed, power := none }
  let pushed := pushPendingRun found.state newRun
  have hConsumedMax : consumed ≤ PY_LIST_MAX := by omega
  have hRunNat : newRun.len.toNat = consumed := by
    simpa [newRun] using listSizeWord_toNat hConsumedMax
  have hPolicy := pushPendingRun_preserves_policy found.state scanned newRun
    hFound.readyToPush
  have hFoundMinrun : found.state.minrunState = call.minrunState := by
    simp only [MergeState.minrunState]
    rw [hFound.stableFrame.listlen, hFound.stableFrame.mrCurrent,
      hFound.stableFrame.mrE, hFound.stableFrame.mrMask]
  refine
    { inputSizeLower := hInputLower
      inputSizeMax := hInputMax
      listlen := ?_
      listlenNonnegative := ?_
      basekeys := ?_
      dataExtent := ?_
      cursor := ?_
      partition := ?_
      pendingLayout := ?_
      poweredPrefix := ?_
      tempInvariant := ?_
      tempLive := ?_
      physicalSlotsBound := ?_
      hasValues := ?_
      valuesMode := ?_
      comparator := ?_
      adaptive := ?_ }
  · simpa [pushed, pushPendingRun] using
      (show found.state.listlen.toNat = inputSize by
        rw [hFound.stableFrame.listlen]
        exact hListlen)
  · have hword : found.state.listlen.Nonnegative := by
      rw [hFound.stableFrame.listlen]
      exact hListNonnegative
    simpa [pushed, pushPendingRun] using hword
  · simpa [pushed, pushPendingRun] using
      hFound.stableFrame.basekeys.trans hBasekeys
  · simpa [pushed, pushPendingRun] using
      hFound.stableFrame.dataSize.trans hExtent
  · have hbase : found.state.basekeys = call.basekeys :=
      hFound.stableFrame.basekeys
    simp only [pushPendingRun]
    rw [hbase, hCursor]
    omega
  · omega
  · simpa [pushed, hRunNat] using hPolicy.2.1
  · simpa [pushed] using hPolicy.2.2.1
  · simpa [pushed, pushPendingRun] using hFound.tempInvariant
  · simpa [pushed, pushPendingRun] using hFound.tempLive
  · have hFoundBound := hFound.physicalSlotsBound hPhysical
    simpa [pushed, pushPendingRun, MergeMemorySnapshot.ofState] using
      hFoundBound
  · simpa [pushed, pushPendingRun] using
      hFound.hasValuesFrame.trans hHasValues
  · simpa [pushed, pushPendingRun] using hFound.valuesMode
  · simpa [pushed, pushPendingRun] using
      hFound.stableFrame.comparator.trans hComparator
  · intro hRemaining
    rcases hAdaptiveAfter hRemaining with ⟨calls, hAdaptive⟩
    refine ⟨calls, ?_⟩
    change AdaptiveMinrunScanInvariant found.state.listlen calls
      (scanned + consumed) found.state.minrunState
    rw [hFound.stableFrame.listlen, hFoundMinrun]
    exact hAdaptive

/-! ## Scan induction -/

private theorem pendingLayout_of_frame
    (before after : MergeState κ ν) (scanned : Nat)
    (hLayout : PendingLayout before scanned)
    (hListlen : after.listlen = before.listlen)
    (hBasekeys : after.basekeys = before.basekeys)
    (hDataSize : after.data.entries.size = before.data.entries.size)
    (hPending : after.pending.toList = before.pending.toList) :
    PendingLayout after scanned := by
  unfold PendingLayout at hLayout ⊢
  rw [hListlen, hBasekeys, hDataSize, hPending]
  exact hLayout

private theorem poweredPrefix_of_frame
    (before after : MergeState κ ν)
    (hPowered : PoweredPrefix before)
    (hListlen : after.listlen = before.listlen)
    (hBasekeys : after.basekeys = before.basekeys)
    (hPending : after.pending.toList = before.pending.toList) :
    PoweredPrefix after := by
  unfold PoweredPrefix at hPowered ⊢
  rw [hListlen, hBasekeys, hPending]
  exact hPowered

private theorem listSortScanTraced_safe_core :
    ∀ (fuel : Nat) (state : MergeState κ ν) (lo scanned remaining : Nat)
      (reverse : Bool) (inputSize : Nat) (lt : BoolComparator κ)
      (hasKeyfunc : Bool),
      ListSortScanInvariant lt hasKeyfunc inputSize state lo scanned remaining →
      remaining ≤ fuel →
      ∃ result,
        ListSortExecutionPost
          (listSortScanTraced? fuel state lo remaining reverse inputSize)
          state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
  intro fuel
  induction fuel with
  | zero =>
      intro state lo scanned remaining reverse inputSize lt hasKeyfunc hInv
        hFuel
      have hRemaining : remaining = 0 := by omega
      subst remaining
      exact listSortScanTraced_terminal_safe 0 state lo scanned reverse
        inputSize lt hasKeyfunc hInv
  | succ fuel ih =>
      intro state lo scanned remaining reverse inputSize lt hasKeyfunc hInv
        hFuel
      by_cases hRemaining : remaining = 0
      · subst remaining
        exact listSortScanTraced_terminal_safe (fuel + 1) state lo scanned
          reverse inputSize lt hasKeyfunc hInv
      · have hRemainingPositive : 0 < remaining := Nat.pos_of_ne_zero hRemaining
        have hLo : lo = scanned := by
          have hCursor := hInv.cursor
          rw [hInv.basekeys] at hCursor
          omega
        have hRemainingInput : remaining ≤ inputSize := by
          have hPartition := hInv.partition
          omega
        have hRange : SortSlice.RangeInBounds state.data (Int.ofNat lo)
            remaining := by
          constructor
          · exact Int.natCast_nonneg lo
          · rw [hInv.dataExtent]
            have hPartition := hInv.partition
            have hNat : lo + remaining ≤ inputSize := by omega
            simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
              (Int.ofNat_le.mpr hNat)
        have hRemainingSsize : remaining ≤ PY_SSIZE_T_MAX := by
          have hMaxLe : PY_LIST_MAX ≤ PY_SSIZE_T_MAX := by
            norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
          exact hRemainingInput.trans (hInv.inputSizeMax.trans hMaxLe)
        rcases countRun_safe state state.data (Int.ofNat lo) remaining hRange
            hRemainingPositive hRemainingSsize hInv.valuesMode with
          ⟨counted, hCounted⟩
        let countedState : MergeState κ ν := { state with data := counted.slice }
        have hCountedLayout : PendingLayout countedState scanned := by
          apply pendingLayout_of_frame state countedState scanned
              hInv.pendingLayout
          · rfl
          · rfl
          · exact hCounted.sizeEq
          · rfl
        have hCountedPowered : PoweredPrefix countedState := by
          exact poweredPrefix_of_frame state countedState hInv.poweredPrefix rfl
            rfl rfl
        rcases hInv.adaptive hRemainingPositive with ⟨calls, hAdaptive⟩
        have hAdaptiveCounted : AdaptiveMinrunScanInvariant
            countedState.listlen calls scanned countedState.minrunState := by
          simpa [countedState, MergeState.minrunState] using hAdaptive
        have hActive : scanned < countedState.listlen.toNat := by
          simp only [countedState]
          rw [hInv.listlen]
          have hPartition := hInv.partition
          omega
        have hStep := adaptiveMinrun_step_facts hAdaptiveCounted hActive
        let nextMinrun := minrunNext countedState.minrunState
        let installed := installMinrunState countedState nextMinrun.state
        let target := nextMinrun.result.toNat
        let force := if remaining ≤ target then remaining else target
        have hTargetPositive : 1 ≤ target := by
          simpa [target, nextMinrun] using hStep.targetPositive
        have hTargetMax : target ≤ MAX_MINRUN.toNat := by
          simpa [target, nextMinrun] using hStep.targetMax
        have hForcePositive : 1 ≤ force := by
          dsimp [force]
          split <;> omega
        have hForceRemaining : force ≤ remaining := by
          dsimp [force]
          split <;> omega
        have hForceMax : force ≤ MAX_MINRUN.toNat := by
          dsimp [force]
          split <;> omega
        have hInstalledListlen : installed.listlen = state.listlen := by
          simp [installed, nextMinrun, countedState, installMinrunState,
            minrunNext, MergeState.minrunState]
        have hInstalledBasekeys : installed.basekeys = state.basekeys := by
          simp [installed, countedState, installMinrunState]
        have hInstalledDataSize : installed.data.entries.size =
            state.data.entries.size := by
          simpa [installed, countedState, installMinrunState] using
            hCounted.sizeEq
        have hInstalledPending : installed.pending.toList =
            state.pending.toList := by
          simp [installed, countedState, installMinrunState]
        have hInstalledLayout : PendingLayout installed scanned := by
          exact pendingLayout_of_frame state installed scanned
            hInv.pendingLayout hInstalledListlen hInstalledBasekeys
            hInstalledDataSize hInstalledPending
        have hInstalledPowered : PoweredPrefix installed := by
          exact poweredPrefix_of_frame state installed hInv.poweredPrefix
            hInstalledListlen hInstalledBasekeys hInstalledPending
        have hInstalledInv : TempStorageInv installed.a installed.alloced := by
          simpa [installed, countedState, installMinrunState] using
            hInv.tempInvariant
        have hInstalledLive : installed.a.Live := by
          simpa [installed, countedState, installMinrunState] using hInv.tempLive
        have hInstalledPhysical :
            (MergeMemorySnapshot.ofState installed).PhysicalBound := by
          simpa [installed, countedState, installMinrunState,
            MergeMemorySnapshot.PhysicalBound, MergeMemorySnapshot.ofState] using
            hInv.physicalSlotsBound
        have hInstalledMode :
            SortSlice.ValuesModeInvariant installed.a.hasValues installed.data := by
          simpa [installed, countedState, installMinrunState] using
            hCounted.valuesMode
        have hInstalledMax : installed.listlen.toNat ≤ PY_LIST_MAX := by
          rw [hInstalledListlen, hInv.listlen]
          exact hInv.inputSizeMax
        have hInstalledBase : lo = installed.basekeys + scanned := by
          rw [hInstalledBasekeys]
          exact hInv.cursor
        have hInstalledWithin : scanned + force ≤ installed.listlen.toNat := by
          rw [hInstalledListlen, hInv.listlen]
          have hPartition := hInv.partition
          omega
        have hCountedWithin : counted.length ≤ remaining :=
          hCounted.lengthBounds.2
        have hCountedValid :
            ¬ (counted.length = 0 ∨ remaining < counted.length) := by
          have hCountedPositive := hCounted.lengthBounds.1
          omega
        have hRunWordNonnegative :
            PySSize.Nonnegative (BitVec.ofNat 64 counted.length) := by
          apply listSizeWord_nonnegative
          exact hCountedWithin.trans
            (hRemainingInput.trans hInv.inputSizeMax)
        have hTargetNonnegative : nextMinrun.result.Nonnegative := by
          apply pySSize_nonnegative_of_toNat_le_maxMinrun
          simpa [target] using hTargetMax
        have hSignedCompare := pySSize_slt_eq_nat_lt
          (BitVec.ofNat 64 counted.length : PySSize) nextMinrun.result
          hRunWordNonnegative hTargetNonnegative
        by_cases hExtend :
            (BitVec.ofNat 64 counted.length : PySSize).slt nextMinrun.result =
              true
        · have hRunLtTarget : counted.length < target := by
            rw [hSignedCompare,
              listSizeWord_toNat
                (hCountedWithin.trans
                  (hRemainingInput.trans hInv.inputSizeMax))] at hExtend
            exact of_decide_eq_true hExtend
          have hRunForce : counted.length ≤ force := by
            dsimp [force]
            split <;> omega
          have hInstalledRange : SortSlice.RangeInBounds installed.data
              (Int.ofNat lo) force := by
            constructor
            · exact Int.natCast_nonneg lo
            · have hExtent : installed.data.entries.size = inputSize := by
                rw [hInstalledDataSize, hInv.dataExtent]
              have hFullRange : SortSlice.RangeInBounds installed.data
                  (Int.ofNat lo) remaining :=
                hRange.of_size_eq hInstalledDataSize
              have hEnd := hFullRange.2
              have hCast : Int.ofNat force ≤ Int.ofNat remaining :=
                Int.ofNat_le.mpr hForceRemaining
              omega
          rcases binarysort_safe installed installed.data (Int.ofNat lo) force
              counted.length hForcePositive hRunForce hForceMax
              hInstalledRange hInstalledMode with ⟨sorted, hSorted⟩
          let extended : MergeState κ ν := { installed with data := sorted.slice }
          have hExtendedLayout : PendingLayout extended scanned := by
            apply pendingLayout_of_frame installed extended scanned
                hInstalledLayout
            · rfl
            · rfl
            · exact hSorted.sizeEq
            · rfl
          have hExtendedPowered : PoweredPrefix extended := by
            exact poweredPrefix_of_frame installed extended hInstalledPowered rfl
              rfl rfl
          have hExtendedInv : TempStorageInv extended.a extended.alloced := by
            simpa [extended] using hInstalledInv
          have hExtendedLive : extended.a.Live := by
            simpa [extended] using hInstalledLive
          have hExtendedPhysical :
              (MergeMemorySnapshot.ofState extended).PhysicalBound := by
            simpa [extended, MergeMemorySnapshot.PhysicalBound,
              MergeMemorySnapshot.ofState] using hInstalledPhysical
          have hExtendedMode :
              SortSlice.ValuesModeInvariant extended.a.hasValues extended.data := by
            simpa [extended] using hSorted.valuesMode
          have hExtendedBase : lo = extended.basekeys + scanned := by
            simpa [extended] using hInstalledBase
          have hExtendedMax : extended.listlen.toNat ≤ PY_LIST_MAX := by
            simpa [extended] using hInstalledMax
          have hExtendedWithin : scanned + force ≤
              extended.listlen.toNat := by
            simpa [extended] using hInstalledWithin
          have hAdaptiveAfter : 0 < remaining - force →
              ∃ nextCalls, AdaptiveMinrunScanInvariant extended.listlen
                nextCalls (scanned + force) extended.minrunState := by
            intro hStillActive
            refine ⟨calls + 1, ?_⟩
            have hNotClipped : ¬ remaining ≤ target := by
              intro hClipped
              have hForceEq : force = remaining := by
                simp [force, hClipped]
              rw [hForceEq] at hStillActive
              simp at hStillActive
            have hForceEq : force = target := by
              simp [force, hNotClipped]
            have hTargetConsumed : nextMinrun.result.toNat ≤ force := by
              simpa [target] using hForceEq.symm.le
            have hNextScanned : scanned + force ≤
                countedState.listlen.toNat := by
              simp only [countedState]
              rw [hInv.listlen]
              have hPartition := hInv.partition
              omega
            have hAdvanced := hAdaptiveCounted.advance (consumed := force)
              hActive hTargetConsumed hNextScanned
            have hExtendedListlen : extended.listlen = state.listlen := by
              simpa [extended] using hInstalledListlen
            have hExtendedMinrun : extended.minrunState = nextMinrun.state := by
              change installed.minrunState = nextMinrun.state
              exact (installMinrunState_frame countedState nextMinrun.state).1
            rw [hExtendedListlen, hExtendedMinrun]
            simpa [nextMinrun, countedState] using hAdvanced
          have hAfter : ∃ result,
              ListSortExecutionPost
                (listSortAfterExtensionTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  lo remaining reverse inputSize
                  counted.length target
                  (extended, force, sorted.fuelExhausted))
                extended.a.hasValues (MergeMemorySnapshot.ofState extended)
                  result := by
            rw [hSorted.resultFuel]
            apply listSortAfterExtensionTraced_safe
            · exact hExtendedMax
            · exact hExtendedLayout
            · exact hExtendedPowered
            · exact hExtendedBase
            · exact hForcePositive
            · exact hExtendedWithin
            · exact hForceRemaining
            · exact hExtendedInv
            · exact hExtendedLive
            · exact hExtendedPhysical
            · exact hExtendedMode
            · intro found
              dsimp only
              intro hFound
              have hNextInv := listSortScanInvariant_after_push lt hasKeyfunc
                inputSize extended lo scanned remaining force found
                hInv.inputSizeLower hInv.inputSizeMax
                (by simpa [extended] using
                  (show installed.listlen.toNat = inputSize by
                    rw [hInstalledListlen, hInv.listlen]))
                (by simpa [extended, hInstalledListlen] using
                  hInv.listlenNonnegative)
                (by simpa [extended, hInstalledBasekeys] using hInv.basekeys)
                (by simpa [extended] using
                  (show sorted.slice.entries.size = inputSize by
                    rw [hSorted.sizeEq, hInstalledDataSize, hInv.dataExtent]))
                hExtendedBase hInv.partition hForcePositive hForceRemaining
                hExtendedPhysical
                (by simpa [extended, installed, countedState,
                    installMinrunState] using hInv.hasValues)
                (by simpa [extended, installed, countedState,
                    installMinrunState] using hInv.comparator)
                hAdaptiveAfter hFound
              apply ih _ _ _ _ _ _ _ _ hNextInv
              omega
          rcases hAfter with ⟨result, hAfter⟩
          have hInstalledExtendedSnapshot :
              MergeMemorySnapshot.ofState extended =
                MergeMemorySnapshot.ofState installed :=
            mergeMemorySnapshot_eq_of_storage_frame installed extended rfl rfl
              (by simpa [extended] using hSorted.sizeEq) hInstalledMode
              hExtendedMode
          have hAfterFromInstalled :
              ListSortExecutionPost
                (listSortAfterExtensionTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  lo remaining reverse inputSize
                  counted.length target
                  (extended, force, sorted.fuelExhausted))
                installed.a.hasValues (MergeMemorySnapshot.ofState extended)
                result := by
            simpa [extended] using hAfter
          have hSortedSafe : ListSortTraceSafety
              (binarysortTraced? installed installed.data (Int.ofNat lo)
                force counted.length) :=
            ListSortTraceSafety.of_noPushes _ hSorted.traceFuel
              hSorted.accessesInBounds hSorted.tempAccessesLive hSorted.noPushes
          have hSortedEvents :
              (binarysortTraced? installed installed.data (Int.ofNat lo)
                force counted.length).trace.memoryEvents = [] :=
            binarysortTraced_memoryEvents_eq_nil _ _ _ _ _
          have hSortedSegment :
              (binarysortTraced? installed installed.data (Int.ofNat lo)
                force counted.length).trace.MergeMemorySegment
                  (MergeMemorySnapshot.ofState installed)
                  (MergeMemorySnapshot.ofState extended) := by
            simpa [hInstalledExtendedSnapshot] using
              (mergeMemorySegment_of_events_nil
                (binarysortTraced? installed installed.data (Int.ofNat lo)
                  force counted.length)
                (MergeMemorySnapshot.ofState installed) hSortedEvents)
          have hBinaryPost : ListSortExecutionPost
              ((binarysortTraced? installed installed.data (Int.ofNat lo)
                  force counted.length).bind fun sorted =>
                listSortAfterExtensionTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  lo remaining reverse inputSize
                  counted.length target
                  ({ installed with data := sorted.slice }, force,
                    sorted.fuelExhausted))
              installed.a.hasValues (MergeMemorySnapshot.ofState installed)
              result := by
            apply ListSortExecutionPost.bind_segment _ _ sorted result
              installed.a.hasValues (MergeMemorySnapshot.ofState installed)
                (MergeMemorySnapshot.ofState extended)
              hSorted.resultEq hSortedSafe
              (memoryEventsValid_of_events_nil _ _ hSortedEvents)
              (mergeMemoryEventsBounded_of_events_nil _ hSortedEvents)
              hSortedSegment
            simpa [extended] using hAfterFromInstalled
          have hPostCountSafe : ListSortTraceSafety
              (listSortAfterCountTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                state lo remaining reverse inputSize counted) := by
            have hBind := ListSortTraceSafety.bind
              (binarysortTraced? installed installed.data (Int.ofNat lo)
                force counted.length)
              (fun sorted =>
                listSortAfterExtensionTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  lo remaining reverse inputSize
                  counted.length target
                  ({ installed with data := sorted.slice }, force,
                    sorted.fuelExhausted))
              sorted hSorted.resultEq hSortedSafe hAfter.traceSafety
            simpa [listSortAfterCountTraced?, hCounted.resultFuel,
              hCountedValid, countedState, nextMinrun, installed, target,
              force, hExtend, extended] using hBind
          have hStateInstalledSnapshot :
              MergeMemorySnapshot.ofState installed =
                MergeMemorySnapshot.ofState state :=
            mergeMemorySnapshot_eq_of_storage_frame state installed
              (by simp [installed, countedState, installMinrunState])
              (by simp [installed, countedState, installMinrunState])
              hInstalledDataSize hInv.valuesMode hInstalledMode
          have hPostCountMemory : ListSortExecutionPost
              (listSortAfterCountTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                state lo remaining reverse inputSize counted)
              state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
            have hBinaryPost' : ListSortExecutionPost
                ((binarysortTraced? installed installed.data (Int.ofNat lo)
                    force counted.length).bind fun sorted =>
                  listSortAfterExtensionTraced?
                    (fun nextState nextLo nextRemaining =>
                      listSortScanTraced? fuel nextState nextLo nextRemaining
                        reverse inputSize)
                    lo remaining reverse inputSize
                    counted.length target
                    ({ installed with data := sorted.slice }, force,
                      sorted.fuelExhausted))
                state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
              exact ListSortExecutionPost.rebase _ _ _ _ _
                hStateInstalledSnapshot hBinaryPost
            simpa [listSortAfterCountTraced?, hCounted.resultFuel,
              hCountedValid, countedState, nextMinrun, installed, target,
              force, hExtend, extended] using hBinaryPost'
          have hCountSafe : ListSortTraceSafety
              (countRunTraced? state state.data (Int.ofNat lo) remaining) :=
            ListSortTraceSafety.of_noPushes _ hCounted.traceFuel
              hCounted.accessesInBounds hCounted.tempAccessesLive
              hCounted.noPushes
          have hCountEvents :
              (countRunTraced? state state.data (Int.ofNat lo)
                remaining).trace.memoryEvents = [] :=
            countRunTraced_memoryEvents_eq_nil _ _ _ _
          have hWholePost : ListSortExecutionPost
              ((countRunTraced? state state.data (Int.ofNat lo) remaining).bind
                fun counted => listSortAfterCountTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  state lo remaining reverse inputSize counted)
              state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
            exact ListSortExecutionPost.bind_segment _ _ counted result
              state.a.hasValues (MergeMemorySnapshot.ofState state)
              (MergeMemorySnapshot.ofState state) hCounted.resultEq hCountSafe
              (memoryEventsValid_of_events_nil _ _ hCountEvents)
              (mergeMemoryEventsBounded_of_events_nil _ hCountEvents)
              (mergeMemorySegment_of_events_nil _ _ hCountEvents)
              hPostCountMemory
          have hWholeSafe := ListSortTraceSafety.bind
            (countRunTraced? state state.data (Int.ofNat lo) remaining)
            (fun counted => listSortAfterCountTraced?
              (fun nextState nextLo nextRemaining =>
                listSortScanTraced? fuel nextState nextLo nextRemaining
                  reverse inputSize)
              state lo remaining reverse inputSize counted)
            counted hCounted.resultEq hCountSafe hPostCountSafe
          have hPostCountEq :
              (listSortAfterCountTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                state lo remaining reverse inputSize counted).result =
                some result := by
            have hBinaryResult :
                ((binarysortTraced? installed installed.data (Int.ofNat lo)
                    force counted.length).bind fun sorted =>
                  listSortAfterExtensionTraced?
                    (fun nextState nextLo nextRemaining =>
                      listSortScanTraced? fuel nextState nextLo nextRemaining
                        reverse inputSize)
                    lo remaining reverse inputSize
                    counted.length target
                    ({ installed with data := sorted.slice }, force,
                      sorted.fuelExhausted)).result = some result :=
              (traceResult_bind_result_of_eq_some _ _ sorted
                hSorted.resultEq).trans hAfter.resultEq
            simpa [listSortAfterCountTraced?, hCounted.resultFuel,
              hCountedValid, countedState, nextMinrun, installed, target,
              force, hExtend, extended] using hBinaryResult
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                rw [listSortScanTraced?, if_neg hRemaining]
                exact (traceResult_bind_result_of_eq_some _ _ counted
                  hCounted.resultEq).trans hPostCountEq
              returnCode := hAfter.returnCode
              resultFuel := hAfter.resultFuel
              traceSafety := by
                simpa [listSortScanTraced?, hRemaining] using hWholeSafe
              memoryEventsValid := by
                simpa [listSortScanTraced?, hRemaining] using
                  hWholePost.memoryEventsValid
              memoryEventsBounded := by
                simpa [listSortScanTraced?, hRemaining] using
                  hWholePost.memoryEventsBounded
              memoryTail := by
                simpa [listSortScanTraced?, hRemaining] using
                  hWholePost.memoryTail
              finalTempInvariant := hAfter.finalTempInvariant
              finalValuesMode := hAfter.finalValuesMode
              finalHasValues := hAfter.finalHasValues.trans (by
                simp [extended, installed, countedState, installMinrunState])
              finalPhysicalBound := hAfter.finalPhysicalBound }
        · have hRunNotLtTarget : ¬ counted.length < target := by
            intro hlt
            apply hExtend
            rw [hSignedCompare,
              listSizeWord_toNat
                (hCountedWithin.trans
                  (hRemainingInput.trans hInv.inputSizeMax))]
            exact decide_eq_true hlt
          have hTargetRun : target ≤ counted.length := by omega
          have hAdaptiveAfter : 0 < remaining - counted.length →
              ∃ nextCalls, AdaptiveMinrunScanInvariant installed.listlen
                nextCalls (scanned + counted.length) installed.minrunState := by
            intro _
            refine ⟨calls + 1, ?_⟩
            have hNextScanned : scanned + counted.length ≤
                countedState.listlen.toNat := by
              simp only [countedState]
              rw [hInv.listlen]
              have hPartition := hInv.partition
              omega
            have hAdvanced := hAdaptiveCounted.advance hActive hTargetRun
              hNextScanned
            have hInstalledMinrun : installed.minrunState = nextMinrun.state :=
              (installMinrunState_frame countedState nextMinrun.state).1
            rw [hInstalledListlen, hInstalledMinrun]
            simpa [nextMinrun, countedState] using hAdvanced
          have hAfter : ∃ result,
              ListSortExecutionPost
                (listSortAfterExtensionTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  lo remaining reverse inputSize
                  counted.length target
                  (installed, counted.length, false))
                installed.a.hasValues (MergeMemorySnapshot.ofState installed)
                  result := by
            apply listSortAfterExtensionTraced_safe
            · exact hInstalledMax
            · exact hInstalledLayout
            · exact hInstalledPowered
            · exact hInstalledBase
            · exact hCounted.lengthBounds.1
            · rw [hInstalledListlen, hInv.listlen]
              have hPartition := hInv.partition
              omega
            · exact hCounted.lengthBounds.2
            · exact hInstalledInv
            · exact hInstalledLive
            · exact hInstalledPhysical
            · exact hInstalledMode
            · intro found
              dsimp only
              intro hFound
              have hNextInv := listSortScanInvariant_after_push lt hasKeyfunc
                inputSize installed lo scanned remaining counted.length found
                hInv.inputSizeLower hInv.inputSizeMax
                (by rw [hInstalledListlen, hInv.listlen])
                (by rw [hInstalledListlen]; exact hInv.listlenNonnegative)
                (by rw [hInstalledBasekeys]; exact hInv.basekeys)
                (by rw [hInstalledDataSize, hInv.dataExtent])
                hInstalledBase hInv.partition hCounted.lengthBounds.1
                hCounted.lengthBounds.2
                hInstalledPhysical
                (by simpa [installed, countedState, installMinrunState] using
                  hInv.hasValues)
                (by simpa [installed, countedState, installMinrunState] using
                  hInv.comparator)
                hAdaptiveAfter hFound
              apply ih _ _ _ _ _ _ _ _ hNextInv
              omega
          rcases hAfter with ⟨result, hAfter⟩
          have hStateInstalledSnapshot :
              MergeMemorySnapshot.ofState installed =
                MergeMemorySnapshot.ofState state :=
            mergeMemorySnapshot_eq_of_storage_frame state installed
              (by simp [installed, countedState, installMinrunState])
              (by simp [installed, countedState, installMinrunState])
              hInstalledDataSize hInv.valuesMode hInstalledMode
          have hPostCountMemory : ListSortExecutionPost
              (listSortAfterCountTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                state lo remaining reverse inputSize counted)
              state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
            have hAfter' : ListSortExecutionPost
                (listSortAfterExtensionTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  lo remaining reverse inputSize
                  counted.length target
                  (installed, counted.length, false))
                state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
              exact ListSortExecutionPost.rebase _ _ _ _ _
                hStateInstalledSnapshot (by
                  simpa [installed, countedState, installMinrunState] using
                    hAfter)
            simpa [listSortAfterCountTraced?, hCounted.resultFuel,
              hCountedValid, countedState, nextMinrun, installed, target,
              force, hExtend] using hAfter'
          have hPostCountSafe : ListSortTraceSafety
              (listSortAfterCountTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                state lo remaining reverse inputSize counted) := by
            simpa [listSortAfterCountTraced?, hCounted.resultFuel,
              hCountedValid, countedState, nextMinrun, installed, target,
              force, hExtend] using hAfter.traceSafety
          have hCountSafe : ListSortTraceSafety
              (countRunTraced? state state.data (Int.ofNat lo) remaining) :=
            ListSortTraceSafety.of_noPushes _ hCounted.traceFuel
              hCounted.accessesInBounds hCounted.tempAccessesLive
              hCounted.noPushes
          have hCountEvents :
              (countRunTraced? state state.data (Int.ofNat lo)
                remaining).trace.memoryEvents = [] :=
            countRunTraced_memoryEvents_eq_nil _ _ _ _
          have hWholePost : ListSortExecutionPost
              ((countRunTraced? state state.data (Int.ofNat lo) remaining).bind
                fun counted => listSortAfterCountTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  state lo remaining reverse inputSize counted)
              state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
            exact ListSortExecutionPost.bind_segment _ _ counted result
              state.a.hasValues (MergeMemorySnapshot.ofState state)
              (MergeMemorySnapshot.ofState state) hCounted.resultEq hCountSafe
              (memoryEventsValid_of_events_nil _ _ hCountEvents)
              (mergeMemoryEventsBounded_of_events_nil _ hCountEvents)
              (mergeMemorySegment_of_events_nil _ _ hCountEvents)
              hPostCountMemory
          have hWholeSafe := ListSortTraceSafety.bind
            (countRunTraced? state state.data (Int.ofNat lo) remaining)
            (fun counted => listSortAfterCountTraced?
              (fun nextState nextLo nextRemaining =>
                listSortScanTraced? fuel nextState nextLo nextRemaining
                  reverse inputSize)
              state lo remaining reverse inputSize counted)
            counted hCounted.resultEq hCountSafe hPostCountSafe
          have hPostCountEq :
              (listSortAfterCountTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                state lo remaining reverse inputSize counted).result =
                some result := by
            simpa [listSortAfterCountTraced?, hCounted.resultFuel,
              hCountedValid, countedState, nextMinrun, installed, target,
              force, hExtend] using hAfter.resultEq
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                rw [listSortScanTraced?, if_neg hRemaining]
                exact (traceResult_bind_result_of_eq_some _ _ counted
                  hCounted.resultEq).trans hPostCountEq
              returnCode := hAfter.returnCode
              resultFuel := hAfter.resultFuel
              traceSafety := by
                simpa [listSortScanTraced?, hRemaining] using hWholeSafe
              memoryEventsValid := by
                simpa [listSortScanTraced?, hRemaining] using
                  hWholePost.memoryEventsValid
              memoryEventsBounded := by
                simpa [listSortScanTraced?, hRemaining] using
                  hWholePost.memoryEventsBounded
              memoryTail := by
                simpa [listSortScanTraced?, hRemaining] using
                  hWholePost.memoryTail
              finalTempInvariant := hAfter.finalTempInvariant
              finalValuesMode := hAfter.finalValuesMode
              finalHasValues := hAfter.finalHasValues.trans (by
                simp [installed, countedState, installMinrunState])
              finalPhysicalBound := hAfter.finalPhysicalBound }

private theorem initialMergeState_scanInvariant
    (lt : BoolComparator κ) (hasKeyfunc : Bool) (input : SortSlice κ ν)
    (hLower : 2 ≤ input.entries.size)
    (hMax : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    ListSortScanInvariant lt hasKeyfunc input.entries.size
      (initialMergeState lt hasKeyfunc input).1 0 0 input.entries.size := by
  have hPackage := initialMergeState_package lt hasKeyfunc input hMax hMode
  refine
    { inputSizeLower := hLower
      inputSizeMax := hMax
      listlen := hPackage.listlenRoundtrip
      listlenNonnegative := hPackage.listlenNonnegative
      basekeys := hPackage.basekeys
      dataExtent := by simp
      cursor := by simp [hPackage.basekeys]
      partition := by simp
      pendingLayout := hPackage.pendingLayout
      poweredPrefix := hPackage.poweredPrefix
      tempInvariant := hPackage.tempInvariant
      tempLive := hPackage.tempLive
      physicalSlotsBound := by
        simpa [MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hPackage.physicalSlotsBound
      hasValues := hPackage.hasValues
      valuesMode := hPackage.valuesMode
      comparator := hPackage.comparator
      adaptive := ?_ }
  intro _
  refine ⟨0, ?_⟩
  have hInitial := adaptiveMinrunScanInvariant_initial
    (initialMergeState lt hasKeyfunc input).1.listlen
    hPackage.listlenNonnegative (by simpa [hPackage.listlenRoundtrip] using hMax)
  simpa [hPackage.minrunState] using hInitial

private theorem ListSortScanInvariant.withData
    {lt : BoolComparator κ} {hasKeyfunc : Bool} {inputSize : Nat}
    {state : MergeState κ ν} {lo scanned remaining : Nat}
    (hInv : ListSortScanInvariant lt hasKeyfunc inputSize state lo scanned
      remaining)
    (slice : SortSlice κ ν)
    (hSize : slice.entries.size = state.data.entries.size)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ListSortScanInvariant lt hasKeyfunc inputSize { state with data := slice }
      lo scanned remaining := by
  refine
    { inputSizeLower := hInv.inputSizeLower
      inputSizeMax := hInv.inputSizeMax
      listlen := hInv.listlen
      listlenNonnegative := hInv.listlenNonnegative
      basekeys := hInv.basekeys
      dataExtent := by simpa using hSize.trans hInv.dataExtent
      cursor := hInv.cursor
      partition := hInv.partition
      pendingLayout := ?_
      poweredPrefix := hInv.poweredPrefix
      tempInvariant := hInv.tempInvariant
      tempLive := hInv.tempLive
      physicalSlotsBound := by
        change state.a.physicalSlots ≤
          PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES
        exact hInv.physicalSlotsBound
      hasValues := hInv.hasValues
      valuesMode := hMode
      comparator := hInv.comparator
      adaptive := hInv.adaptive }
  exact pendingLayout_of_frame state { state with data := slice } scanned
    hInv.pendingLayout rfl rfl hSize rfl

private theorem listSortImplTraced_success
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν)
    (hSize : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    ∃ result,
      ListSortImplExecutionPost lt reverse hasKeyfunc input result := by
  let state := (initialMergeState lt hasKeyfunc input).1
  have hPackage := initialMergeState_package lt hasKeyfunc input hSize hMode
  have hStopped : (initialMergeState lt hasKeyfunc input).2 = true :=
    hPackage.minrunStopped
  have hInitialActive :
      (MergeMemorySnapshot.ofState state).ActiveCore hasKeyfunc := by
    apply MergeMemorySnapshot.activeCore_ofState hasKeyfunc state
    · simpa [state] using hPackage.tempInvariant
    · simpa [state] using hPackage.tempLive
    · simpa [state] using hPackage.hasValues
    · simpa [state] using hPackage.valuesMode
  by_cases hSmall : input.entries.size < 2
  · rcases finishListSortExecutionPost state reverse input.entries.size
        (by simp [state])
        (by simpa [state] using hPackage.tempInvariant)
        (by simpa [state] using hPackage.tempLive)
        (by simpa [state, MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hPackage.physicalSlotsBound)
        (by simpa [state] using hPackage.valuesMode) with
      ⟨result, hFinished⟩
    refine ⟨result, ?_⟩
    exact
      { resultEq := by
          simpa [listSortImplTraced?, hSize, hStopped, hSmall, state] using
            hFinished.resultEq
        returnCode := hFinished.returnCode
        resultFuel := hFinished.resultFuel
        traceSafety := by
          simpa [listSortImplTraced?, hSize, hStopped, hSmall, state] using
            (ListSortTraceSafety.prependMemoryEvent
              (finishListSortTraced? state reverse input.entries.size 0 false)
              (.initial (MergeMemorySnapshot.ofState state))
              hFinished.traceSafety)
        memoryLifecycle := by
          have hTailValid :
              (finishListSortTraced? state reverse input.entries.size 0 false).trace.memoryEventsValid
                hasKeyfunc := by
            simpa [state, hPackage.hasValues] using hFinished.memoryEventsValid
          have hLifecycle := AccessTrace.mergeMemoryLifecycle_prepend_initial
            hasKeyfunc (MergeMemorySnapshot.ofState state)
            (MergeMemorySnapshot.ofState result.state)
            (finishListSortTraced? state reverse input.entries.size 0 false).trace
            hFinished.memoryTail hInitialActive hTailValid
            hFinished.memoryEventsBounded
          simpa [listSortImplTraced?, hSize, hStopped, hSmall, state,
            TraceResult.prependMemoryEvent] using hLifecycle
        finalTempInvariant := hFinished.finalTempInvariant
        finalValuesMode := hFinished.finalValuesMode
        finalHasValues := hFinished.finalHasValues.trans (by
          simp [state])
        finalPhysicalBound := hFinished.finalPhysicalBound }
  · have hLower : 2 ≤ input.entries.size := by omega
    have hInitialInv := initialMergeState_scanInvariant lt hasKeyfunc input
      hLower hSize hMode
    cases reverse with
    | false =>
        rcases listSortScanTraced_safe_core input.entries.size state 0 0
            input.entries.size false input.entries.size lt hasKeyfunc
            (by simpa [state] using hInitialInv) (le_refl _) with
          ⟨result, hScan⟩
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simpa [listSortImplTraced?, hSize, hStopped, hSmall, state]
                using hScan.resultEq
            returnCode := hScan.returnCode
            resultFuel := hScan.resultFuel
            traceSafety := by
              simpa [listSortImplTraced?, hSize, hStopped, hSmall, state]
                using (ListSortTraceSafety.prependMemoryEvent
                  (listSortScanTraced? input.entries.size state 0
                    input.entries.size false input.entries.size)
                  (.initial (MergeMemorySnapshot.ofState state))
                  hScan.traceSafety)
            memoryLifecycle := by
              have hScanValid :
                  (listSortScanTraced? input.entries.size state 0
                    input.entries.size false input.entries.size).trace.memoryEventsValid
                    hasKeyfunc := by
                simpa [state, hPackage.hasValues] using hScan.memoryEventsValid
              have hLifecycle := AccessTrace.mergeMemoryLifecycle_prepend_initial
                hasKeyfunc (MergeMemorySnapshot.ofState state)
                (MergeMemorySnapshot.ofState result.state)
                (listSortScanTraced? input.entries.size state 0
                  input.entries.size false input.entries.size).trace
                hScan.memoryTail hInitialActive hScanValid
                hScan.memoryEventsBounded
              simpa [listSortImplTraced?, hSize, hStopped, hSmall, state,
                TraceResult.prependMemoryEvent] using hLifecycle
            finalTempInvariant := hScan.finalTempInvariant
            finalValuesMode := hScan.finalValuesMode
            finalHasValues := hScan.finalHasValues.trans (by
              simp [state])
            finalPhysicalBound := hScan.finalPhysicalBound }
    | true =>
        have hRange : SortSlice.RangeInBounds state.data 0 input.entries.size := by
          constructor
          · omega
          · rw [show state.data.entries.size = input.entries.size by
                simp [state]]
            simp
        rcases sortsliceReverse_safe state.a.hasValues state.data 0
            input.entries.size hRange
            (by simpa [state] using hPackage.valuesMode) with
          ⟨reversed, hReversed⟩
        let reversedState : MergeState κ ν :=
          { state with data := reversed.slice }
        have hReversedInv : ListSortScanInvariant lt hasKeyfunc
            input.entries.size reversedState 0 0 input.entries.size := by
          apply ListSortScanInvariant.withData
              (by simpa [state] using hInitialInv) reversed.slice
          · simpa [state] using hReversed.sizeEq
          · simpa [reversedState] using hReversed.valuesMode
        rcases listSortScanTraced_safe_core input.entries.size reversedState 0 0
            input.entries.size true input.entries.size lt hasKeyfunc
            hReversedInv (le_refl _) with ⟨result, hScan⟩
        have hInitialReverseEq :
            (listSortInitialReverseTraced? state input.entries.size).result =
              some reversed := by
          simpa [listSortInitialReverseTraced?] using hReversed.resultEq
        have hInitialReverseSafe : ListSortTraceSafety
            (listSortInitialReverseTraced? state input.entries.size) := by
          apply ListSortTraceSafety.of_noPushes
          · simpa [listSortInitialReverseTraced?] using hReversed.traceFuel
          · simpa [listSortInitialReverseTraced?] using
              hReversed.accessesInBounds
          · simpa [listSortInitialReverseTraced?] using
              hReversed.tempAccessesLive
          · simpa [listSortInitialReverseTraced?] using hReversed.noPushes
        let afterReverse : ReverseSliceResult κ ν →
            TraceResult (ListSortImplResult κ ν) := fun reversed =>
          let nextState : MergeState κ ν := { state with data := reversed.slice }
          if reversed.fuelExhausted then
            finishListSortTraced? nextState true input.entries.size (-1) true
          else
            listSortScanTraced? input.entries.size nextState 0
              input.entries.size true input.entries.size
        have hAfterReverseSafe : ListSortTraceSafety (afterReverse reversed) := by
          simpa [afterReverse, hReversed.resultFuel, reversedState] using
            hScan.traceSafety
        have hCombined : ListSortTraceSafety
            ((listSortInitialReverseTraced? state input.entries.size).bind
              afterReverse) :=
          ListSortTraceSafety.bind _ _ reversed hInitialReverseEq
            hInitialReverseSafe hAfterReverseSafe
        have hReverseEvents :
            (listSortInitialReverseTraced? state input.entries.size).trace.memoryEvents =
              [] := by
          simpa [listSortInitialReverseTraced?] using
            (sortsliceReverseTraced_memoryEvents_eq_nil state.a.hasValues
              state.data 0 input.entries.size)
        have hReversedSnapshot :
            MergeMemorySnapshot.ofState reversedState =
              MergeMemorySnapshot.ofState state :=
          mergeMemorySnapshot_eq_of_storage_frame state reversedState rfl rfl
            (by simpa [reversedState] using hReversed.sizeEq)
            (by simpa [state] using hPackage.valuesMode)
            (by simpa [reversedState] using hReversed.valuesMode)
        have hReverseSegment :
            (listSortInitialReverseTraced? state input.entries.size).trace.MergeMemorySegment
              (MergeMemorySnapshot.ofState state)
              (MergeMemorySnapshot.ofState reversedState) := by
          simpa [hReversedSnapshot] using
            (mergeMemorySegment_of_events_nil
              (listSortInitialReverseTraced? state input.entries.size)
              (MergeMemorySnapshot.ofState state) hReverseEvents)
        have hScanAfterReverse : ListSortExecutionPost (afterReverse reversed)
            state.a.hasValues (MergeMemorySnapshot.ofState reversedState)
            result := by
          simpa [afterReverse, hReversed.resultFuel, reversedState] using hScan
        have hCombinedPost : ListSortExecutionPost
            ((listSortInitialReverseTraced? state input.entries.size).bind
              afterReverse)
            state.a.hasValues (MergeMemorySnapshot.ofState state) result := by
          exact ListSortExecutionPost.bind_segment _ _ reversed result
            state.a.hasValues (MergeMemorySnapshot.ofState state)
              (MergeMemorySnapshot.ofState reversedState)
            hInitialReverseEq hInitialReverseSafe
            (memoryEventsValid_of_events_nil _ _ hReverseEvents)
            (mergeMemoryEventsBounded_of_events_nil _ hReverseEvents)
            hReverseSegment hScanAfterReverse
        have hAfterReverseEq : (afterReverse reversed).result = some result := by
          simpa [afterReverse, hReversed.resultFuel, reversedState] using
            hScan.resultEq
        have hCombinedEq :
            ((listSortInitialReverseTraced? state input.entries.size).bind
              afterReverse).result = some result :=
          (traceResult_bind_result_of_eq_some _ _ reversed
            hInitialReverseEq).trans hAfterReverseEq
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simpa [listSortImplTraced?, hSize, hStopped, hSmall, state,
                afterReverse] using hCombinedEq
            returnCode := hScan.returnCode
            resultFuel := hScan.resultFuel
            traceSafety := by
              simpa [listSortImplTraced?, hSize, hStopped, hSmall, state,
                afterReverse] using (ListSortTraceSafety.prependMemoryEvent
                  ((listSortInitialReverseTraced? state input.entries.size).bind
                    afterReverse)
                  (.initial (MergeMemorySnapshot.ofState state)) hCombined)
            memoryLifecycle := by
              have hCombinedValid :
                  ((listSortInitialReverseTraced? state input.entries.size).bind
                    afterReverse).trace.memoryEventsValid hasKeyfunc := by
                simpa [state, hPackage.hasValues] using
                  hCombinedPost.memoryEventsValid
              have hLifecycle := AccessTrace.mergeMemoryLifecycle_prepend_initial
                hasKeyfunc (MergeMemorySnapshot.ofState state)
                (MergeMemorySnapshot.ofState result.state)
                ((listSortInitialReverseTraced? state input.entries.size).bind
                  afterReverse).trace
                hCombinedPost.memoryTail hInitialActive hCombinedValid
                hCombinedPost.memoryEventsBounded
              simpa [listSortImplTraced?, hSize, hStopped, hSmall, state,
                afterReverse, TraceResult.prependMemoryEvent] using hLifecycle
            finalTempInvariant := hScan.finalTempInvariant
            finalValuesMode := hScan.finalValuesMode
            finalHasValues := hScan.finalHasValues.trans (by
              simp [reversedState, state])
            finalPhysicalBound := hScan.finalPhysicalBound }

/-! ## Public certificates -/

theorem listSortScanTraced_safe_of_helper_erasure
    (hFound : ∀ (state : MergeState κ ν) (runLength : Nat),
      (foundNewRunTraced? state runLength).erase =
        foundNewRun? state runLength)
    (hCollapse : ∀ (state : MergeState κ ν),
      (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state)
    (fuel : Nat) (state : MergeState κ ν) (lo scanned remaining : Nat)
    (reverse : Bool) (inputSize : Nat) (lt : BoolComparator κ)
    (hasKeyfunc : Bool)
    (hInv : ListSortScanInvariant lt hasKeyfunc inputSize state lo scanned
      remaining)
    (hFuel : remaining ≤ fuel) :
    ∃ result,
      ListSortScanSafetyPost fuel state lo remaining reverse inputSize result := by
  rcases listSortScanTraced_safe_core fuel state lo scanned remaining reverse
      inputSize lt hasKeyfunc hInv hFuel with ⟨result, hResult⟩
  exact ⟨result,
    { resultEq := hResult.resultEq
      returnCode := hResult.returnCode
      resultFuel := hResult.resultFuel
      traceSafety := hResult.traceSafety
      memoryEventsValid := hResult.memoryEventsValid
      memoryEventsBounded := hResult.memoryEventsBounded
      memoryTail := hResult.memoryTail
      exactErasure := erase_listSortScanTraced_of_helper_erasure hFound
        hCollapse fuel state lo remaining reverse inputSize
      finalTempInvariant := hResult.finalTempInvariant
      finalValuesMode := hResult.finalValuesMode
      finalHasValues := hResult.finalHasValues
      finalPhysicalBound := hResult.finalPhysicalBound }⟩

theorem listSortImplTraced_safe_of_helper_erasure
    (hFound : ∀ (state : MergeState κ ν) (runLength : Nat),
      (foundNewRunTraced? state runLength).erase =
        foundNewRun? state runLength)
    (hCollapse : ∀ (state : MergeState κ ν),
      (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state)
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν)
    (hSize : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    ∃ result, ListSortImplSafetyPost lt reverse hasKeyfunc input result := by
  rcases listSortImplTraced_success lt reverse hasKeyfunc input hSize hMode with
    ⟨result, hResult⟩
  exact ⟨result,
    { resultEq := hResult.resultEq
      returnCode := hResult.returnCode
      resultFuel := hResult.resultFuel
      traceSafety := hResult.traceSafety
      memoryLifecycle := hResult.memoryLifecycle
      exactErasure := erase_listSortImplTraced_of_helper_erasure hFound
        hCollapse lt reverse hasKeyfunc input
      finalTempInvariant := hResult.finalTempInvariant
      finalValuesMode := hResult.finalValuesMode
      finalHasValues := hResult.finalHasValues
      finalPhysicalBound := hResult.finalPhysicalBound }⟩

theorem listSortTraced_safe_of_helper_erasure
    (hFound : ∀ (state : MergeState κ ν) (runLength : Nat),
      (foundNewRunTraced? state runLength).erase =
        foundNewRun? state runLength)
    (hCollapse : ∀ (state : MergeState κ ν),
      (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state)
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ListSortSafetyPost lt reverse input result := by
  rcases listSortImplTraced_safe_of_helper_erasure hFound hCollapse lt reverse
      input.hasKeyfunc input.slice hSize input.valuesMode with
    ⟨result, hResult⟩
  exact ⟨result,
    { resultEq := hResult.resultEq
      returnCode := hResult.returnCode
      resultFuel := hResult.resultFuel
      traceSafety := hResult.traceSafety
      memoryLifecycle := hResult.memoryLifecycle
      exactErasure := erase_listSortTraced_of_helper_erasure hFound hCollapse
        lt reverse input
      finalTempInvariant := hResult.finalTempInvariant
      finalValuesMode := hResult.finalValuesMode
      finalHasValues := hResult.finalHasValues
      finalPhysicalBound := hResult.finalPhysicalBound }⟩

/-! The unconditional helper bridges turn the parameterized structural
erasure and safety theorems above into the compact public API. -/

theorem erase_listSortScanTraced
    (fuel : Nat) (state : MergeState κ ν) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat) :
    (listSortScanTraced? fuel state lo remaining reverse inputSize).erase =
      listSortScan? fuel state lo remaining reverse inputSize := by
  exact erase_listSortScanTraced_of_helper_erasure erase_foundNewRunTraced
    erase_mergeForceCollapseTraced fuel state lo remaining reverse inputSize

theorem erase_listSortImplTraced
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) :
    (listSortImplTraced? lt reverse hasKeyfunc input).erase =
      listSortImpl? lt reverse hasKeyfunc input := by
  exact erase_listSortImplTraced_of_helper_erasure erase_foundNewRunTraced
    erase_mergeForceCollapseTraced lt reverse hasKeyfunc input

theorem erase_listSortTraced
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν) :
    (listSortTraced? lt reverse input).erase = listSort? lt reverse input := by
  exact erase_listSortTraced_of_helper_erasure erase_foundNewRunTraced
    erase_mergeForceCollapseTraced lt reverse input

theorem listSortScanTraced_safe
    (fuel : Nat) (state : MergeState κ ν) (lo scanned remaining : Nat)
    (reverse : Bool) (inputSize : Nat) (lt : BoolComparator κ)
    (hasKeyfunc : Bool)
    (hInv : ListSortScanInvariant lt hasKeyfunc inputSize state lo scanned
      remaining)
    (hFuel : remaining ≤ fuel) :
    ∃ result,
      ListSortScanSafetyPost fuel state lo remaining reverse inputSize result :=
  listSortScanTraced_safe_of_helper_erasure erase_foundNewRunTraced
    erase_mergeForceCollapseTraced fuel state lo scanned remaining reverse
      inputSize lt hasKeyfunc hInv hFuel

theorem listSortImplTraced_safe
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν)
    (hSize : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    ∃ result, ListSortImplSafetyPost lt reverse hasKeyfunc input result :=
  listSortImplTraced_safe_of_helper_erasure erase_foundNewRunTraced
    erase_mergeForceCollapseTraced lt reverse hasKeyfunc input hSize hMode

theorem listSortTraced_safe
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ListSortSafetyPost lt reverse input result :=
  listSortTraced_safe_of_helper_erasure erase_foundNewRunTraced
    erase_mergeForceCollapseTraced lt reverse input hSize

end CPythonListsort

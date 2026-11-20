/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortTermination

/-!
# Aggregate temporary merge-memory safety

This module is the public projection of the literal merge-memory history
carried by `listSortImplTraced?`.  It does not define another evaluator or a
separately supplied history: every lifecycle field below refers directly to
the `memoryEvents` stored in the actual top-level execution trace.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Exact merge-memory lifecycle projected from the raw top-level safety
certificate.  This declaration gives the roadmap's lifecycle node a unique
theorem boundary, separate from both the event-validity support vocabulary and
the broader termination theorem that supplies the proof. -/
theorem listSortImpl_mergeMemory_lifecycle
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν)
    (hSize : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    ∃ result,
      (listSortImplTraced? lt reverse hasKeyfunc input).result = some result ∧
      (listSortImplTraced? lt reverse hasKeyfunc input).trace.MergeMemoryLifecycle
        hasKeyfunc
        (MergeMemorySnapshot.ofState
          (initialMergeState lt hasKeyfunc input).1)
        (MergeMemorySnapshot.ofState result.state) := by
  rcases listSortImplTraced_safe lt reverse hasKeyfunc input hSize hMode with
    ⟨result, hSafe⟩
  exact ⟨result, hSafe.resultEq, hSafe.memoryLifecycle⟩

/-- Complete temporary-memory certificate for the raw top-level evaluator.

The two public premises of `listSortImpl_mergeMemory_safe` are deliberately
not stored here: this postcondition records only observable execution facts
and the representation facts proved for the returned state. -/
structure ListSortImplMergeMemorySafetyPost
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (result : ListSortImplResult κ ν) : Prop where
  /-- The actual traced evaluator returns this result. -/
  resultEq :
    (listSortImplTraced? lt reverse hasKeyfunc input).result = some result
  /-- The modeled C return code is successful. -/
  returnCode : result.returnCode = 0
  /-- The returned result does not report fuel exhaustion. -/
  resultFuel : result.fuelExhausted = false
  /-- The actual trace does not report fuel exhaustion. -/
  traceFuel :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.fuelExhausted =
      false
  /-- Erasing the trace recovers the unchanged raw evaluator. -/
  exactErasure :
    (listSortImplTraced? lt reverse hasKeyfunc input).erase =
      listSortImpl? lt reverse hasKeyfunc input
  /-- The unchanged raw evaluator itself returns the same successful result. -/
  rawResultEq : listSortImpl? lt reverse hasKeyfunc input = some result
  /-- Every recorded array access is inside its recorded extent. -/
  allAccessesInBounds :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.allAccessesInBounds
  /-- No temporary payload access occurs while backing is released. -/
  tempPayloadAccessesLive :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.tempPayloadAccessesLive
  /-- Every physically recorded post-push stack depth is at most 61. -/
  stackDepthMax :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.stackDepthMax ≤ 61
  /-- The proved depth is strictly below CPython's pending-stack capacity. -/
  stackDepthBelowCapacity : 61 < MAX_MERGE_PENDING
  /-- The concrete storage installed by `merge_init` already satisfies the
  selected-platform physical pointer-slot ceiling. -/
  initialPhysicalBound :
    (MergeMemorySnapshot.ofState
      (initialMergeState lt hasKeyfunc input).1).PhysicalBound
  /-- The actual trace is exactly initializer, continuous directional calls,
  and terminal cleanup, at the concrete state snapshots shown here. -/
  memoryLifecycle :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.MergeMemoryLifecycle
      hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt hasKeyfunc input).1)
      (MergeMemorySnapshot.ofState result.state)
  /-- Cleanup preserves the temporary-storage representation invariant. -/
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  /-- The final main array still agrees with the retained values mode. -/
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  /-- The retained mode bit is exactly the mode established by initialization. -/
  finalHasValues : result.state.a.hasValues = hasKeyfunc
  /-- The final concrete allocation observation remains within the selected
  platform's physical pointer-slot bound. -/
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound
  /-- Every merge `memcpy` callsite crosses distinct temporary/main backing;
  same-backing bulk movement is routed through `memmove`. -/
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν

/-- Complete temporary-memory certificate at the validated public boundary. -/
structure ListSortMergeMemorySafetyPost
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (result : ListSortImplResult κ ν) : Prop where
  /-- The actual validated-input traced evaluator returns this result. -/
  resultEq : (listSortTraced? lt reverse input).result = some result
  /-- The modeled C return code is successful. -/
  returnCode : result.returnCode = 0
  /-- The returned result does not report fuel exhaustion. -/
  resultFuel : result.fuelExhausted = false
  /-- The actual trace does not report fuel exhaustion. -/
  traceFuel : (listSortTraced? lt reverse input).trace.fuelExhausted = false
  /-- Erasing the trace recovers the unchanged public evaluator. -/
  exactErasure :
    (listSortTraced? lt reverse input).erase = listSort? lt reverse input
  /-- The unchanged public evaluator itself returns the same successful result. -/
  rawResultEq : listSort? lt reverse input = some result
  /-- Every recorded array access is inside its recorded extent. -/
  allAccessesInBounds :
    (listSortTraced? lt reverse input).trace.allAccessesInBounds
  /-- No temporary payload access occurs while backing is released. -/
  tempPayloadAccessesLive :
    (listSortTraced? lt reverse input).trace.tempPayloadAccessesLive
  /-- Every physically recorded post-push stack depth is at most 61. -/
  stackDepthMax :
    (listSortTraced? lt reverse input).trace.stackDepthMax ≤ 61
  /-- The proved depth is strictly below CPython's pending-stack capacity. -/
  stackDepthBelowCapacity : 61 < MAX_MERGE_PENDING
  /-- The concrete storage installed by `merge_init` already satisfies the
  selected-platform physical pointer-slot ceiling. -/
  initialPhysicalBound :
    (MergeMemorySnapshot.ofState
      (initialMergeState lt input.hasKeyfunc input.slice).1).PhysicalBound
  /-- The actual trace is exactly initializer, continuous directional calls,
  and terminal cleanup, at the concrete state snapshots shown here. -/
  memoryLifecycle :
    (listSortTraced? lt reverse input).trace.MergeMemoryLifecycle
      input.hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt input.hasKeyfunc input.slice).1)
      (MergeMemorySnapshot.ofState result.state)
  /-- Cleanup preserves the temporary-storage representation invariant. -/
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  /-- The final main array still agrees with the retained values mode. -/
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  /-- The retained mode bit is exactly the validated input mode. -/
  finalHasValues : result.state.a.hasValues = input.hasKeyfunc
  /-- The final concrete allocation observation remains within the selected
  platform's physical pointer-slot bound. -/
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound
  /-- The closed merge bulk-copy inventory satisfies callsite provenance. -/
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν

/-- Raw aggregate theorem.  Its only proof premises are the selected-platform
input-size bound and the explicit keyed/unkeyed values-mode invariant. -/
theorem listSortImpl_mergeMemory_safe
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν)
    (hSize : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    ∃ result,
      ListSortImplMergeMemorySafetyPost lt reverse hasKeyfunc input result := by
  rcases listSortImplTraced_safe lt reverse hasKeyfunc input hSize hMode with
    ⟨result, hSafe⟩
  exact ⟨result,
    { resultEq := hSafe.resultEq
      returnCode := hSafe.returnCode
      resultFuel := hSafe.resultFuel
      traceFuel := hSafe.traceSafety.fuel
      exactErasure := hSafe.exactErasure
      rawResultEq := by
        calc
          listSortImpl? lt reverse hasKeyfunc input =
              (listSortImplTraced? lt reverse hasKeyfunc input).erase :=
            hSafe.exactErasure.symm
          _ = (listSortImplTraced? lt reverse hasKeyfunc input).result := rfl
          _ = some result := hSafe.resultEq
      allAccessesInBounds := hSafe.traceSafety.accessesInBounds
      tempPayloadAccessesLive := hSafe.traceSafety.tempAccessesLive
      stackDepthMax := hSafe.traceSafety.stackDepth
      stackDepthBelowCapacity := by norm_num [MAX_MERGE_PENDING]
      initialPhysicalBound := by
        have hInitial := initialMergeState_package lt hasKeyfunc input hSize hMode
        simpa [MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hInitial.physicalSlotsBound
      memoryLifecycle := hSafe.memoryLifecycle
      finalTempInvariant := hSafe.finalTempInvariant
      finalValuesMode := hSafe.finalValuesMode
      finalHasValues := hSafe.finalHasValues
      finalPhysicalBound := hSafe.finalPhysicalBound
      memcpyProvenance :=
        mergeMemcpyCallsiteProvenance (κ := κ) (ν := ν) }⟩

/-- Public aggregate theorem.  The values-mode premise is discharged by the
validated `ListSortInput`; the only separate proof premise is the platform
size bound. -/
theorem listSort_mergeMemory_safe
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ListSortMergeMemorySafetyPost lt reverse input result := by
  rcases listSortTraced_safe lt reverse input hSize with ⟨result, hSafe⟩
  exact ⟨result,
    { resultEq := hSafe.resultEq
      returnCode := hSafe.returnCode
      resultFuel := hSafe.resultFuel
      traceFuel := hSafe.traceSafety.fuel
      exactErasure := hSafe.exactErasure
      rawResultEq := by
        calc
          listSort? lt reverse input =
              (listSortTraced? lt reverse input).erase :=
            hSafe.exactErasure.symm
          _ = (listSortTraced? lt reverse input).result := rfl
          _ = some result := hSafe.resultEq
      allAccessesInBounds := hSafe.traceSafety.accessesInBounds
      tempPayloadAccessesLive := hSafe.traceSafety.tempAccessesLive
      stackDepthMax := hSafe.traceSafety.stackDepth
      stackDepthBelowCapacity := by norm_num [MAX_MERGE_PENDING]
      initialPhysicalBound := by
        have hInitial := initialMergeState_package lt input.hasKeyfunc
          input.slice hSize input.valuesMode
        simpa [MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hInitial.physicalSlotsBound
      memoryLifecycle := hSafe.memoryLifecycle
      finalTempInvariant := hSafe.finalTempInvariant
      finalValuesMode := hSafe.finalValuesMode
      finalHasValues := hSafe.finalHasValues
      finalPhysicalBound := hSafe.finalPhysicalBound
      memcpyProvenance :=
        mergeMemcpyCallsiteProvenance (κ := κ) (ν := ν) }⟩

/-- Ordinary unkeyed-array specialization of the public aggregate theorem. -/
theorem listSort_unkeyedArray_mergeMemory_safe
    (lt : BoolComparator κ) (reverse : Bool) (keys : Array κ)
    (hSize : keys.size ≤ PY_LIST_MAX) :
    ∃ result,
      ListSortMergeMemorySafetyPost lt reverse (ListSortInput.unkeyed keys)
        result := by
  apply listSort_mergeMemory_safe lt reverse (ListSortInput.unkeyed keys)
  simpa [ListSortInput.unkeyed, ListSortInput.unkeyedAs] using hSize

/-! ## Exact top-level lifecycle regressions

The two empty-input regressions below are kernel-checked structural proofs.
The three larger executable regressions are deliberately isolated
compiler-checked proof leaves: they evaluate the complete top-level model, but
no theorem or definition consumes them.  They are listed by name in the
roadmap's two-tier proof-trust ledger.
-/

namespace MergeMemoryRegression

/-- Concrete total Boolean comparator used only by the executable witnesses. -/
def natLt (left right : Nat) : Bool := decide (left < right)

/-- Empty ordinary-array input with a fixed payload universe. -/
def emptyUnkeyed : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs #[]

/-- Empty keyed input; its mode bit remains observable even though the
entrywise values-mode invariant is vacuous. -/
def emptyKeyed : ListSortInput Nat Nat :=
  ListSortInput.keyed #[]

/-- Two increasing natural runs whose boundary descends, so the top-level
scan discovers two distinct runs before final collapse. -/
def twoRunKeys (leftLength rightLength : Nat) : Array Nat :=
  (Array.range leftLength |>.map fun key => 1000 + key) ++
    Array.range rightLength

/-- Equal 33-element runs force the left-to-right merge direction. -/
def loInput : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs (twoRunKeys 33 33)

/-- A 33-element left run and 32-element right run force the right-to-left
merge direction. -/
def hiInput : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs (twoRunKeys 33 32)

/-- Observable directional-call projection of the literal top-level trace. -/
def directions {payload : Type} (input : ListSortInput Nat payload) :
    List MergeMemoryDirection :=
  (listSortTraced? natLt false input).trace.memoryEvents.filterMap fun
    | .mergeCall call => some call.direction
    | _ => none

/-- One increasing keyed run used by the repeated-growth fixture. -/
def keyedRun (base length : Nat) : Array (Nat × Nat) :=
  (Array.range length).map fun offset =>
    let key := base + offset
    (key, key)

/-- Four descending-by-block 129-element keyed runs.  The first pair grows
past keyed inline capacity 128; the final 258/258 merge then frees that heap
buffer and grows again. -/
def releasedGrowthInput : ListSortInput Nat Nat :=
  ListSortInput.keyed
    (keyedRun 3000 129 ++ keyedRun 2000 129 ++
      keyedRun 1000 129 ++ keyedRun 0 129)

/-- For every actual directional call, retain the optional freed backing,
the post-`merge_getmem` backing, and its logical cell count. -/
def growthSummaries :
    List (Option TempBacking × TempBacking × Nat) :=
  (listSortTraced? natLt false releasedGrowthInput).trace.memoryEvents.filterMap
    fun
      | .mergeCall call =>
          some (call.intermediateFree.map (·.backing),
            call.afterGetmem.backing, call.afterGetmem.cellsSize)
      | _ => none

end MergeMemoryRegression

/-- Kernel-checked exact empty unkeyed history: initialization is followed
immediately by cleanup, with no directional call between them. -/
theorem listSort_mergeMemory_empty_unkeyed_trace_regression :
    let input := MergeMemoryRegression.emptyUnkeyed
    let state :=
      (initialMergeState MergeMemoryRegression.natLt input.hasKeyfunc
        input.slice).1
    (listSortTraced? MergeMemoryRegression.natLt false input).trace.memoryEvents =
      [.initial (MergeMemorySnapshot.ofState state),
        .cleanup (MergeMemorySnapshot.ofState state)
          (MergeMemorySnapshot.ofState (mergeFreemem state))] := by
  dsimp only
  have hSize : MergeMemoryRegression.emptyUnkeyed.slice.entries.size ≤
      PY_LIST_MAX := by
    simp [MergeMemoryRegression.emptyUnkeyed,
      ListSortInput.unkeyedAs]
  have hPackage := initialMergeState_package MergeMemoryRegression.natLt
    MergeMemoryRegression.emptyUnkeyed.hasKeyfunc
    MergeMemoryRegression.emptyUnkeyed.slice hSize
    MergeMemoryRegression.emptyUnkeyed.valuesMode
  have hSmall : MergeMemoryRegression.emptyUnkeyed.slice.entries.size < 2 := by
    simp [MergeMemoryRegression.emptyUnkeyed,
      ListSortInput.unkeyedAs]
  simp [listSortTraced?, listSortImplTraced?, hSize,
    hPackage.minrunStopped, hSmall, finishListSortTraced?,
    listSortCleanupMemoryEvent, TraceResult.pure,
    TraceResult.appendMemoryEvent, TraceResult.prependMemoryEvent,
    AccessTrace.empty, AccessTrace.singletonMemoryEvent, AccessTrace.compose]

/-- Kernel-checked exact empty keyed history.  Besides excluding any merge
call, the second conjunct pins the otherwise-vacuous keyed mode bit to true. -/
theorem listSort_mergeMemory_empty_keyed_trace_regression :
    let input := MergeMemoryRegression.emptyKeyed
    let state :=
      (initialMergeState MergeMemoryRegression.natLt input.hasKeyfunc
        input.slice).1
    (listSortTraced? MergeMemoryRegression.natLt false input).trace.memoryEvents =
        [.initial (MergeMemorySnapshot.ofState state),
          .cleanup (MergeMemorySnapshot.ofState state)
            (MergeMemorySnapshot.ofState (mergeFreemem state))] ∧
      (MergeMemorySnapshot.ofState state).hasValues = true := by
  dsimp only
  have hSize : MergeMemoryRegression.emptyKeyed.slice.entries.size ≤
      PY_LIST_MAX := by
    simp [MergeMemoryRegression.emptyKeyed, ListSortInput.keyed]
  have hPackage := initialMergeState_package MergeMemoryRegression.natLt
    MergeMemoryRegression.emptyKeyed.hasKeyfunc
    MergeMemoryRegression.emptyKeyed.slice hSize
    MergeMemoryRegression.emptyKeyed.valuesMode
  have hSmall : MergeMemoryRegression.emptyKeyed.slice.entries.size < 2 := by
    simp [MergeMemoryRegression.emptyKeyed, ListSortInput.keyed]
  constructor
  · simp [listSortTraced?, listSortImplTraced?, hSize,
      hPackage.minrunStopped, hSmall, finishListSortTraced?,
      listSortCleanupMemoryEvent, TraceResult.pure,
      TraceResult.appendMemoryEvent, TraceResult.prependMemoryEvent,
      AccessTrace.empty, AccessTrace.singletonMemoryEvent,
      AccessTrace.compose]
  · exact hPackage.hasValues.trans (by
      simp [MergeMemoryRegression.emptyKeyed, ListSortInput.keyed])

/-- Compiler-checked proof leaf: the actual 66-element top-level execution
contains exactly one directional merge event, and it is `merge_lo`. -/
theorem listSort_mergeMemory_lo_event_regression :
    MergeMemoryRegression.directions MergeMemoryRegression.loInput = [.lo] := by
  native_decide

/-- The full aggregate post is independently kernel-inhabited for the same
nontrivial `merge_lo` fixture; it does not consume the executable regression. -/
theorem listSort_mergeMemory_lo_aggregate_regression :
    ∃ result,
      ListSortMergeMemorySafetyPost MergeMemoryRegression.natLt false
        MergeMemoryRegression.loInput result := by
  apply listSort_mergeMemory_safe
  norm_num [MergeMemoryRegression.loInput,
    MergeMemoryRegression.twoRunKeys, ListSortInput.unkeyedAs, PY_LIST_MAX,
    PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]

/-- Compiler-checked proof leaf: the actual 65-element top-level execution
contains exactly one directional merge event, and it is `merge_hi`. -/
theorem listSort_mergeMemory_hi_event_regression :
    MergeMemoryRegression.directions MergeMemoryRegression.hiInput = [.hi] := by
  native_decide

/-- Compiler-checked proof leaf for repeated allocation growth.  The third
actual call frees a live heap allocation to a released snapshot and then
establishes a 258-cell heap allocation. -/
theorem listSort_mergeMemory_released_growth_regression :
    MergeMemoryRegression.growthSummaries =
      [(some .inline, .heap, 129), (none, .heap, 129),
        (some .released, .heap, 258)] := by
  native_decide

end CPythonListsort

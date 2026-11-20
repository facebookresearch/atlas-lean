/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.ListSortTermination

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

end CPythonListsort

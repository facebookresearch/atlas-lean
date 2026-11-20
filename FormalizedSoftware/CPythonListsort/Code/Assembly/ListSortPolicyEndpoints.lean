/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortMergePolicy

/-!
# Exact empty and singleton policy endpoints

The real top-level evaluator bypasses the scan for inputs of length zero or
one.  Consequently both executions have an empty raw policy-event stream.  At
the paper-facing normalization boundary, that same stream denotes an empty
merge plan at length zero and a literal one-leaf plan at length one.

This module pins those two endpoint cases for arbitrary comparators, reverse
flags, and validated keyed or unkeyed inputs.  In particular, the singleton
leaf is semantic normalization: it is not a fabricated `.formed` event.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- The source interval represented by a validated top-level input. -/
def ListSortInput.runSpan (input : ListSortInput κ ν) : RunSpan :=
  { base := 0, len := input.slice.entries.size }

/-- Exact policy-accounting facts shared by the empty and singleton
top-level endpoints.  `expectedPlan` and `expectedLengths` are parameters so
the two public theorems below expose their exact normal forms in their theorem
types rather than hiding them behind an existential. -/
structure ListSortPolicyEndpointPost
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (result : ListSortImplResult κ ν) (expectedPlan : MergePlan)
    (expectedLengths : List Nat) : Prop where
  resultEq : (listSortTraced? lt reverse input).result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  policyEvents :
    (listSortTraced? lt reverse input).trace.policyEvents = []
  normalizedReplay :
    replayTopLevelMergePlan? input.runSpan
        (listSortTraced? lt reverse input).trace.policyEvents =
      some expectedPlan
  rawFormedLengths :
    PolicyEvent.formedLengths
        (listSortTraced? lt reverse input).trace.policyEvents = []
  normalizedFormedLengths :
    topLevelFormedLengths input.runSpan
        (listSortTraced? lt reverse input).trace.policyEvents =
      expectedLengths
  planRunLengths : expectedPlan.runLengths = expectedLengths
  rawLogicalMergeCost :
    PolicyEvent.logicalMergeCost
        (listSortTraced? lt reverse input).trace.policyEvents = 0
  planMergeCost : expectedPlan.mergeCost = 0

/-- A genuine size-zero execution succeeds, emits no policy event, and
normalizes exactly to the empty plan with no formed lengths and zero cost. -/
theorem listSortTraced_policy_empty
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hEmpty : input.slice.entries.size = 0) :
    ∃ result,
      ListSortPolicyEndpointPost lt reverse input result .empty [] := by
  have hSize : input.slice.entries.size ≤ PY_LIST_MAX := by omega
  have hSmall : input.slice.entries.size < 2 := by omega
  have hPackage := initialMergeState_package lt input.hasKeyfunc input.slice
    hSize input.valuesMode
  rcases listSortTraced_safe lt reverse input hSize with
    ⟨result, hResult⟩
  have hPolicy :
      (listSortTraced? lt reverse input).trace.policyEvents = [] := by
    simpa [listSortTraced?, listSortImplTraced?, hSize,
      hPackage.minrunStopped, hSmall,
      TraceResult.policyEvents_prependMemoryEvent] using
      (finishListSortTraced_policyEvents_eq_nil
        (initialMergeState lt input.hasKeyfunc input.slice).1 reverse
        input.slice.entries.size 0 false)
  refine ⟨result, ?_⟩
  refine
    { resultEq := hResult.resultEq
      returnCode := hResult.returnCode
      resultFuel := hResult.resultFuel
      policyEvents := hPolicy
      normalizedReplay := ?_
      rawFormedLengths := ?_
      normalizedFormedLengths := ?_
      planRunLengths := rfl
      rawLogicalMergeCost := ?_
      planMergeCost := rfl }
  · rw [hPolicy]
    change replayTopLevelMergePlan?
      { base := 0, len := input.slice.entries.size } [] = some .empty
    rw [hEmpty]
    exact replayTopLevelMergePlan_empty 0
  · simp [hPolicy]
  · rw [hPolicy]
    change topLevelFormedLengths
      { base := 0, len := input.slice.entries.size } [] = []
    rw [hEmpty]
    exact topLevelFormedLengths_empty 0
  · simp [hPolicy]

/-- A genuine size-one execution succeeds and still emits no policy event.
Its top-level normalization is exactly one leaf of length one, with normalized
formed lengths `[1]` and zero logical or plan cost. -/
theorem listSortTraced_policy_singleton
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSingleton : input.slice.entries.size = 1) :
    ∃ result,
      ListSortPolicyEndpointPost lt reverse input result
        (.tree (.leaf 1)) [1] := by
  have hSize : input.slice.entries.size ≤ PY_LIST_MAX := by
    simp [hSingleton, PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  have hSmall : input.slice.entries.size < 2 := by omega
  have hPackage := initialMergeState_package lt input.hasKeyfunc input.slice
    hSize input.valuesMode
  rcases listSortTraced_safe lt reverse input hSize with
    ⟨result, hResult⟩
  have hPolicy :
      (listSortTraced? lt reverse input).trace.policyEvents = [] := by
    simpa [listSortTraced?, listSortImplTraced?, hSize,
      hPackage.minrunStopped, hSmall,
      TraceResult.policyEvents_prependMemoryEvent] using
      (finishListSortTraced_policyEvents_eq_nil
        (initialMergeState lt input.hasKeyfunc input.slice).1 reverse
        input.slice.entries.size 0 false)
  refine ⟨result, ?_⟩
  refine
    { resultEq := hResult.resultEq
      returnCode := hResult.returnCode
      resultFuel := hResult.resultFuel
      policyEvents := hPolicy
      normalizedReplay := ?_
      rawFormedLengths := ?_
      normalizedFormedLengths := ?_
      planRunLengths := rfl
      rawLogicalMergeCost := ?_
      planMergeCost := rfl }
  · rw [hPolicy]
    change replayTopLevelMergePlan?
      { base := 0, len := input.slice.entries.size } [] =
        some (.tree (.leaf 1))
    rw [hSingleton]
    exact replayTopLevelMergePlan_singleton 0
  · simp [hPolicy]
  · rw [hPolicy]
    change topLevelFormedLengths
      { base := 0, len := input.slice.entries.size } [] = [1]
    rw [hSingleton]
    exact topLevelFormedLengths_singleton 0
  · simp [hPolicy]

end CPythonListsort

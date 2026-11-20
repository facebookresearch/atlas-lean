/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.MergeMemorySafety
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.RuntimeAssert

namespace CPythonListsort

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
def listSort_mergeMemory_lo_event_regression : IO Unit :=
  CPythonListsortTest.assertTrue "listSort_mergeMemory_lo_event_regression" (decide (
    MergeMemoryRegression.directions MergeMemoryRegression.loInput = [.lo]))

#eval listSort_mergeMemory_lo_event_regression

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
def listSort_mergeMemory_hi_event_regression : IO Unit :=
  CPythonListsortTest.assertTrue "listSort_mergeMemory_hi_event_regression" (decide (
    MergeMemoryRegression.directions MergeMemoryRegression.hiInput = [.hi]))

#eval listSort_mergeMemory_hi_event_regression

/-- Compiler-checked proof leaf for repeated allocation growth.  The third
actual call frees a live heap allocation to a released snapshot and then
establishes a 258-cell heap allocation. -/
def listSort_mergeMemory_released_growth_regression : IO Unit :=
  CPythonListsortTest.assertTrue "listSort_mergeMemory_released_growth_regression" (decide (
    MergeMemoryRegression.growthSummaries =
      [(some .inline, .heap, 129), (none, .heap, 129),
        (some .released, .heap, 258)]))

#eval listSort_mergeMemory_released_growth_regression

end CPythonListsort

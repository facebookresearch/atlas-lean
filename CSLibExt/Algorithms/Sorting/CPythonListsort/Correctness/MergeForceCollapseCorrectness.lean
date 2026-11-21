/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.MergeForceCollapseSafety
import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.MergeAtCorrectness

-- Preserve the imported development's original implicit type binders.
set_option autoImplicit true

/-!
# Functional correctness of `merge_force_collapse`

The final collapse repeatedly delegates to the already-correct `merge_at`
implementation.  This module carries the pending-run correctness and complete
entry snapshot through the actual fuel-bounded collapse evaluator; it does not
replace that evaluator by a mathematical fold.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- End-to-end correctness at the final-collapse boundary.  Safety is embedded
verbatim so the semantic result is tied to the real composed trace. -/
structure MergeForceCollapseCorrectnessPost
    (lt : BoolComparator alpha) (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) : Prop where
  safety : MergeForceCollapseSafetyPost pre scanned result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

private structure MergeForceCollapseLoopCorrectnessPost
    (lt : BoolComparator alpha) (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned fuel : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) : Prop where
  resultEq :
    (mergeForceCollapseLoopTraced? fuel pre).result = some result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

private theorem traceResult_bind_result_of_eq_some
    (current : TraceResult α) (next : α → TraceResult β) (value : α)
    (hresult : current.result = some value) :
    (current.bind next).result = (next value).result := by
  change (current.bind next).erase = (next value).erase
  rw [TraceResult.erase_bind]
  change current.result.bind (fun item => (next item).result) = _
  rw [hresult]
  rfl

/-- Semantic loop invariant for the real collapse recursion.  Every recursive
step obtains its next state from `mergeAt_correct`; no independent abstract
merge transition is assumed. -/
private theorem mergeForceCollapseLoop_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (input : Array alpha) (source : SortSlice alpha nu)
    (fuel : Nat) (state : MergeState (Occurrence alpha) nu) (scanned : Nat)
    (hfuel : fuel = state.pending.size)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hnonempty : state.pending.toList ≠ [])
    (hcorrect : PendingRunsCorrect lt input state scanned)
    (hsnapshot : EntrySnapshotPermutation source state.data)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    ∃ result,
      MergeForceCollapseLoopCorrectnessPost lt input source state scanned fuel
        result := by
  induction fuel generalizing state with
  | zero =>
      have hpositive : 0 < state.pending.size := by
        have := List.length_pos_of_ne_nil hnonempty
        simpa using this
      omega
  | succ remaining ih =>
      by_cases hmany : 1 < state.pending.size
      · rcases forceCollapseIndexTraced_safe state hmany with
          ⟨i, hindexResult, _hindexSafe, _hindexErasure, hposition⟩
        rcases mergeAt_correct horder input source state scanned i hcorrect
            hsnapshot hcompare hmax hposition hInv hLive hMode with
          ⟨merged, hmerged⟩
        rcases hmerged.selected with ⟨left, right, hselected⟩
        rcases hselected.pendingSplice with
          ⟨before, after, _hbeforeLength, hbeforePending, hafterPending⟩
        have hremaining : remaining = merged.state.pending.size :=
          mergeForceCollapseLoop_fuel_tracks_merge remaining state merged.state
            before after left right
            ({ left with len := left.len + right.len } : PendingRun)
            (by simpa [Nat.succ_eq_add_one] using hfuel)
            hbeforePending hafterPending
        have hmergedNonempty : merged.state.pending.toList ≠ [] := by
          rw [hafterPending]
          simp
        have hmergedMax : merged.state.listlen.toNat ≤ PY_LIST_MAX := by
          rw [hmerged.safety.stableFrame.listlen]
          exact hmax
        rcases ih merged.state hremaining hmergedMax hmergedNonempty
            hmerged.pendingRunsCorrect hmerged.entrySnapshot
            hmerged.safety.tempInvariant hmerged.safety.tempLive
            hmerged.safety.valuesMode hmerged.comparator with
          ⟨result, hrest⟩
        have hmergeSuccess :
            merged.returnCode = 0 ∧ !merged.fuelExhausted :=
          ⟨hmerged.safety.returnCode,
            by simp [hmerged.safety.resultFuel]⟩
        have hresult :
            (mergeForceCollapseLoopTraced? (remaining + 1) state).result =
              some result := by
          simp only [mergeForceCollapseLoopTraced?, hmany, ite_true]
          rw [traceResult_bind_result_of_eq_some _ _ i hindexResult]
          rw [traceResult_bind_result_of_eq_some _ _ merged
            hmerged.safety.resultEq]
          rw [ite_eq_left hmergeSuccess]
          exact hrest.resultEq
        have hrestFrame : SortSlice.EqualOutsideRange merged.state.data
            result.state.data state.basekeys scanned := by
          simpa [hmerged.safety.stableFrame.basekeys] using hrest.consumedFrame
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simpa [Nat.succ_eq_add_one] using hresult
            pendingRunsCorrect := hrest.pendingRunsCorrect
            entrySnapshot := hrest.entrySnapshot
            comparator := hrest.comparator
            consumedFrame := hmerged.consumedFrame.trans hrestFrame }
      · have hsizeOne : state.pending.size = 1 := by
          have hpositive : 0 < state.pending.size := by
            have := List.length_pos_of_ne_nil hnonempty
            simpa using this
          omega
        let result : MergeForceCollapseResult (Occurrence alpha) nu :=
          { state := state, returnCode := 0, fuelExhausted := false }
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp only [mergeForceCollapseLoopTraced?, hmany, ite_false]
              rfl
            pendingRunsCorrect := by simpa [result] using hcorrect
            entrySnapshot := by simpa [result] using hsnapshot
            comparator := by simpa [result] using hcompare
            consumedFrame := by
              simpa [result] using
                (SortSlice.EqualOutsideRange.refl state.data state.basekeys
                  scanned) }

/-- Functional correctness of the complete final collapse.

The only order hypothesis is the same strict weak order required by each
delegated stable merge.  Storage liveness and representation premises are
consumed by the safety component rather than retained as top-level conclusions.
-/
theorem mergeForceCollapse_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (input : Array alpha) (source : SortSlice alpha nu)
    (state : MergeState (Occurrence alpha) nu) (scanned : Nat)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hnonempty : state.pending.toList ≠ [])
    (hcorrect : PendingRunsCorrect lt input state scanned)
    (hsnapshot : EntrySnapshotPermutation source state.data)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    ∃ result,
      MergeForceCollapseCorrectnessPost lt input source state scanned result := by
  rcases mergeForceCollapseLoop_correct horder input source state.pending.size
      state scanned rfl hmax hnonempty hcorrect hsnapshot hInv hLive hMode
      hcompare with ⟨semanticResult, hsemantic⟩
  rcases mergeForceCollapse_safe state scanned hmax hnonempty hcorrect.layout
      hInv hLive hMode with ⟨safeResult, hsafety⟩
  have hsafetyLoop :
      (mergeForceCollapseLoopTraced? state.pending.size state).result =
        some safeResult := by
    simpa [mergeForceCollapseTraced?] using hsafety.resultEq
  have hresults : safeResult = semanticResult := by
    exact Option.some.inj (hsafetyLoop.symm.trans hsemantic.resultEq)
  subst semanticResult
  exact
    ⟨safeResult,
      { safety := hsafety
        pendingRunsCorrect := hsemantic.pendingRunsCorrect
        entrySnapshot := hsemantic.entrySnapshot
        comparator := hsemantic.comparator
        consumedFrame := hsemantic.consumedFrame }⟩

namespace MergeForceCollapseCorrectnessPost

/-- The unique final run covers the consumed prefix and carries the complete
sorted, stable occurrence specification exported by `PendingRunsCorrect`. -/
theorem finalRunCorrect
    {lt : BoolComparator alpha} {input : Array alpha}
    {source : SortSlice alpha nu}
    {pre : MergeState (Occurrence alpha) nu} {scanned : Nat}
    {result : MergeForceCollapseResult (Occurrence alpha) nu}
    (h : MergeForceCollapseCorrectnessPost lt input source pre scanned result) :
    ∃ run,
      result.state.pending.toList = [run] ∧
      run.base = pre.basekeys ∧
      run.endIndex = pre.basekeys + scanned ∧
      Sorted (occurrenceComparator lt)
        (pendingRunOccurrenceKeys result.state run) ∧
      StableOccurrencePermutation lt
        (canonicalOccurrenceSegment input pre.basekeys scanned)
        (pendingRunOccurrenceKeys result.state run).toList := by
  rcases h.safety.finalRun with ⟨run, hpending, hbase, hend⟩
  have hmember : run ∈ result.state.pending.toList := by
    rw [hpending]
    simp
  have hsorted := h.pendingRunsCorrect.runSorted run hmember
  have hstable := h.pendingRunsCorrect.stableOccurrencePermutation
  refine ⟨run, hpending, hbase, hend, hsorted, ?_⟩
  simpa [pendingOccurrenceKeys, hpending,
    h.safety.stableFrame.basekeys] using hstable

end MergeForceCollapseCorrectnessPost

/-! ## Executable path regressions -/

/-- A singleton stack is a true no-op success of the complete traced
evaluator: the returned state is definitionally the input state. -/
theorem mergeForceCollapseTraced_singleton_noop
    (state : MergeState κ ν) (run : PendingRun)
    (hpending : state.pending.toList = [run]) :
    (mergeForceCollapseTraced? state).result =
      some { state := state, returnCode := 0, fuelExhausted := false } := by
  have hsize : state.pending.size = 1 := by
    have := congrArg List.length hpending
    simpa using this
  simp only [mergeForceCollapseTraced?, hsize,
    mergeForceCollapseLoopTraced?]
  rfl

end CPythonListsort

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.MergeForceCollapseCorrectness
import Code.Correctness.ScanStepCorrectness

/-!
# Correctness of the complete scan and final collapse

This module closes the induction left deliberately open by
`listSortScan_step_correct`.  It follows the actual `listSortScan?` recursion,
uses strict progress to show that the supplied fuel reaches the terminal arm,
and applies `mergeForceCollapse_correct` to the real terminal state.  The
public post retains that pre-finish collapse result, passes an arbitrary
`reverse` flag to the actual cleanup call, and records the successful scan
result.  A separate corollary exposes the simpler forward cleanup state.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Complete correctness certificate for a `listSortScan?` execution.

`terminal` is the state at the real `remaining = 0` call, `collapsed` is the
result returned by the real `mergeForceCollapse?` invocation there, and
`result` is the state after the requested final-reverse/cleanup phase. Retaining
all three keeps the pre-finish sorted/stable run available even though final
reversal changes its order and cleanup may release temporary storage. -/
structure ListSortScanCollapseCorrectnessPost
    (lt : BoolComparator alpha) (source : SortSlice alpha nu)
    (hasKeyfunc : Bool) (inputSize fuel : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (lo scanned remaining : Nat) (reverse : Bool)
    (terminal : MergeState (Occurrence alpha) nu)
    (collapsed : MergeForceCollapseResult (Occurrence alpha) nu)
    (result : ListSortImplResult (Occurrence alpha) nu) : Prop where
  terminalInvariant : ListSortScanCorrectnessInvariant lt source hasKeyfunc
    inputSize terminal inputSize inputSize 0
  collapseCorrectness : MergeForceCollapseCorrectnessPost lt
    (source.entries.map SortSliceEntry.key) source terminal inputSize collapsed
  collapseResultEq : mergeForceCollapse? terminal = some collapsed
  preFinishEquation :
    listSortScan? fuel state lo remaining reverse inputSize =
      finishListSort? collapsed.state reverse inputSize 0 false
  resultEq :
    listSortScan? fuel state lo remaining reverse inputSize = some result
  finishResultEq :
    finishListSort? collapsed.state reverse inputSize 0 false = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  finalRun :
    ∃ run,
      collapsed.state.pending.toList = [run] ∧
      run.base = terminal.basekeys ∧
      run.endIndex = terminal.basekeys + inputSize ∧
      Sorted (occurrenceComparator lt)
        (pendingRunOccurrenceKeys collapsed.state run) ∧
      StableOccurrencePermutation lt
        (canonicalOccurrenceSegment
          (source.entries.map SortSliceEntry.key) terminal.basekeys inputSize)
        (pendingRunOccurrenceKeys collapsed.state run).toList
  collapsedSnapshot : EntrySnapshotPermutation source collapsed.state.data

namespace ListSortScanCollapseCorrectnessPost

/-- The terminal singleton run is the complete collapsed data array.  This
derived consumer lemma packages the full-array sortedness and stability needed
by both forward and reverse top-level correctness; it adds no field to the
approved scan/collapse post. -/
theorem wholeDataCorrect
    {lt : BoolComparator alpha} {source : SortSlice alpha nu}
    {hasKeyfunc : Bool} {inputSize fuel : Nat}
    {state : MergeState (Occurrence alpha) nu}
    {lo scanned remaining : Nat} {reverse : Bool}
    {terminal : MergeState (Occurrence alpha) nu}
    {collapsed : MergeForceCollapseResult (Occurrence alpha) nu}
    {result : ListSortImplResult (Occurrence alpha) nu}
    (h : ListSortScanCollapseCorrectnessPost lt source hasKeyfunc inputSize fuel
      state lo scanned remaining reverse terminal collapsed result) :
    Sorted (occurrenceComparator lt)
        (collapsed.state.data.entries.map SortSliceEntry.key) ∧
      StableOccurrencePermutation lt
        (tagOccurrences (source.entries.map SortSliceEntry.key)).toList
        (collapsed.state.data.entries.map SortSliceEntry.key).toList := by
  rcases h.finalRun with
    ⟨run, hpending, hbase, hend, hsorted, hstable⟩
  have hterminalBase : terminal.basekeys = 0 :=
    h.terminalInvariant.safety.basekeys
  have hcollapsedSize : collapsed.state.data.entries.size = inputSize :=
    h.collapseCorrectness.safety.stableFrame.dataSize.trans
      h.terminalInvariant.safety.dataExtent
  have hrunBase : run.base = 0 := hbase.trans hterminalBase
  have hrunEnd : run.endIndex = inputSize := by
    rw [hend, hterminalBase]
    simp
  have hrunKeys :
      pendingRunOccurrenceKeys collapsed.state run =
        collapsed.state.data.entries.map SortSliceEntry.key := by
    simp [pendingRunOccurrenceKeys, hrunBase, hrunEnd, hcollapsedSize]
  have hsourceSize : source.entries.size = inputSize := by
    have hlength := h.collapsedSnapshot.length_eq
    simpa [EntrySnapshotPermutation, hcollapsedSize,
      tagSortSliceOccurrences] using hlength.symm
  rw [hrunKeys] at hsorted hstable
  constructor
  · exact hsorted
  · have hcanonical :
        canonicalOccurrenceSegment
            (source.entries.map SortSliceEntry.key) 0 inputSize =
          (tagOccurrences (source.entries.map SortSliceEntry.key)).toList := by
      have htagSize :
          (tagOccurrences
            (source.entries.map SortSliceEntry.key)).size = inputSize := by
        simp [tagOccurrences, hsourceSize]
      simp [canonicalOccurrenceSegment,
        Array.extract_eq_self_of_le (show
          (tagOccurrences
            (source.entries.map SortSliceEntry.key)).size ≤ inputSize by
          omega)]
    simpa [hterminalBase, hcanonical] using hstable

end ListSortScanCollapseCorrectnessPost

/-- A validated occurrence-tagged input establishes the complete correctness
invariant at the first scan call.  This is an assembly lemma local to the new
whole-scan layer; it does not strengthen the approved one-step contract. -/
theorem listSortScanCorrectnessInvariant_initial
    (lt : BoolComparator alpha) (input : ListSortInput alpha nu)
    (hLower : 2 ≤ input.slice.entries.size)
    (hMax : input.slice.entries.size ≤ PY_LIST_MAX) :
    ListSortScanCorrectnessInvariant lt input.slice input.hasKeyfunc
      input.slice.entries.size
      (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
        input.withOccurrenceKeys.slice).1
      0 0 input.slice.entries.size := by
  let tagged := input.withOccurrenceKeys
  let state :=
    (initialMergeState (occurrenceComparator lt) input.hasKeyfunc tagged.slice).1
  have hTaggedSize : tagged.slice.entries.size = input.slice.entries.size := by
    simp [tagged, ListSortInput.withOccurrenceKeys]
  have hTaggedMax : tagged.slice.entries.size ≤ PY_LIST_MAX := by
    simpa [hTaggedSize] using hMax
  have hPackage := initialMergeState_package (occurrenceComparator lt)
    input.hasKeyfunc tagged.slice hTaggedMax tagged.valuesMode
  have hSafety : ListSortScanInvariant (occurrenceComparator lt)
      input.hasKeyfunc input.slice.entries.size state 0 0
      input.slice.entries.size := by
    refine
      { inputSizeLower := hLower
        inputSizeMax := hMax
        listlen := by simpa [state, hTaggedSize] using hPackage.listlenRoundtrip
        listlenNonnegative := by simpa [state] using hPackage.listlenNonnegative
        basekeys := by simpa [state] using hPackage.basekeys
        dataExtent := by simp [state, hTaggedSize]
        cursor := by simp [state, hPackage.basekeys]
        partition := by simp
        pendingLayout := by simpa [state] using hPackage.pendingLayout
        poweredPrefix := by simpa [state] using hPackage.poweredPrefix
        tempInvariant := by simpa [state] using hPackage.tempInvariant
        tempLive := by simpa [state] using hPackage.tempLive
        physicalSlotsBound := by
          simpa [state, MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState] using hPackage.physicalSlotsBound
        hasValues := by simp [state]
        valuesMode := by simpa [state] using hPackage.valuesMode
        comparator := by simpa [state] using hPackage.comparator
        adaptive := ?_ }
    intro _
    refine ⟨0, ?_⟩
    have hStateMax : state.listlen.toNat ≤ PY_LIST_MAX := by
      rw [show state.listlen.toNat = tagged.slice.entries.size by
        simpa [state] using hPackage.listlenRoundtrip]
      exact hTaggedMax
    have hInitial := adaptiveMinrunScanInvariant_initial state.listlen
      (by simpa [state] using hPackage.listlenNonnegative)
      hStateMax
    simpa [state, hPackage.minrunState] using hInitial
  have hPending : PendingRunsCorrect lt
      (input.slice.entries.map SortSliceEntry.key) state 0 := by
    refine ⟨hSafety.pendingLayout, ?_, ?_⟩
    · intro run hrun
      have hEmpty : state.pending = #[] := by simpa [state] using hPackage.pending
      simp [hEmpty] at hrun
    · have hEmpty : state.pending = #[] := by simpa [state] using hPackage.pending
      simp [StableOccurrencePermutation, canonicalOccurrenceSegment,
        pendingOccurrenceKeys, hEmpty]
  have hRemainder : ScanRemainderEntriesMatch input.slice state 0 := by
    simpa [state, tagged] using
      scanRemainderEntriesMatch_initial_listSortInput (occurrenceComparator lt)
        input hMax
  have hSnapshot : EntrySnapshotPermutation input.slice state.data := by
    simpa [state, tagged] using
      EntrySnapshotPermutation.initial_merge_state (occurrenceComparator lt) input
  exact
    { safety := hSafety
      pendingRunsCorrect := hPending
      remainderEntries := hRemainder
      entrySnapshot := hSnapshot }

private theorem listSortScan_terminal_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {source : SortSlice alpha nu} {hasKeyfunc : Bool}
    {inputSize fuel : Nat}
    {state : MergeState (Occurrence alpha) nu}
    {lo scanned : Nat} {reverse : Bool}
    (inv : ListSortScanCorrectnessInvariant lt source hasKeyfunc inputSize state
      lo scanned 0) :
    ∃ collapsed result,
      ListSortScanCollapseCorrectnessPost lt source hasKeyfunc inputSize fuel
        state lo scanned 0 reverse state collapsed result := by
  have hscanned : scanned = inputSize := by
    have := inv.safety.partition
    omega
  have hlo : lo = inputSize := by
    rw [inv.safety.cursor, inv.safety.basekeys, hscanned]
    simp
  have hpending : state.pending.toList ≠ [] := by
    apply inv.pendingRunsCorrect.layout.pending_nonempty
    have := inv.safety.inputSizeLower
    omega
  rcases mergeForceCollapse_correct horder
      (source.entries.map SortSliceEntry.key) source state inputSize
      (by simpa [inv.safety.listlen] using inv.safety.inputSizeMax)
      hpending
      (by simpa [hscanned] using inv.pendingRunsCorrect)
      inv.entrySnapshot inv.safety.tempInvariant inv.safety.tempLive
      inv.safety.valuesMode inv.safety.comparator with
    ⟨collapsed, hcollapsed⟩
  have hcollapseRaw : mergeForceCollapse? state = some collapsed := by
    rw [← hcollapsed.safety.exactErasure]
    exact hcollapsed.safety.resultEq
  have hscanFinish :
      listSortScan? fuel state lo 0 reverse inputSize =
        finishListSort? collapsed.state reverse inputSize 0 false := by
    cases fuel <;>
      simp [listSortScan?, hcollapseRaw, hcollapsed.safety.returnCode,
        hcollapsed.safety.resultFuel]
  rcases listSortScanTraced_safe fuel state lo scanned 0 reverse inputSize
      (occurrenceComparator lt) hasKeyfunc inv.safety (Nat.zero_le _) with
    ⟨result, hresult⟩
  have hscanResult :
      listSortScan? fuel state lo 0 reverse inputSize = some result := by
    rw [← hresult.exactErasure]
    exact hresult.resultEq
  have hfinishResult :
      finishListSort? collapsed.state reverse inputSize 0 false = some result :=
    hscanFinish.symm.trans hscanResult
  have hfinalRun :=
    MergeForceCollapseCorrectnessPost.finalRunCorrect hcollapsed
  refine ⟨collapsed, result, ?_⟩
  exact
    { terminalInvariant := by simpa [hlo, hscanned] using inv
      collapseCorrectness := hcollapsed
      collapseResultEq := hcollapseRaw
      preFinishEquation := hscanFinish
      resultEq := hscanResult
      finishResultEq := hfinishResult
      returnCode := hresult.returnCode
      resultFuel := hresult.resultFuel
      finalRun := by simpa using hfinalRun
      collapsedSnapshot := hcollapsed.entrySnapshot }

/-- Repeating the public one-step correctness theorem reaches the actual
terminal `mergeForceCollapse?` call and then the actual finish call for either
value of `reverse`. No storage, layout, or semantic premise is added outside
the public combined scan invariant. -/
theorem listSortScan_complete_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {source : SortSlice alpha nu} {hasKeyfunc : Bool}
    {inputSize fuel : Nat}
    {state : MergeState (Occurrence alpha) nu}
    {lo scanned remaining : Nat} {reverse : Bool}
    (inv : ListSortScanCorrectnessInvariant lt source hasKeyfunc inputSize state
      lo scanned remaining)
    (hFuel : remaining ≤ fuel) :
    ∃ terminal collapsed result,
      ListSortScanCollapseCorrectnessPost lt source hasKeyfunc inputSize fuel
        state lo scanned remaining reverse terminal collapsed result := by
  induction fuel generalizing state lo scanned remaining with
  | zero =>
      have hremaining : remaining = 0 := by omega
      subst remaining
      rcases listSortScan_terminal_correct horder inv with
        ⟨collapsed, result, hpost⟩
      exact ⟨state, collapsed, result, hpost⟩
  | succ nextFuel ih =>
      by_cases hremaining : remaining = 0
      · subst remaining
        rcases listSortScan_terminal_correct horder inv with
          ⟨collapsed, result, hpost⟩
        exact ⟨state, collapsed, result, hpost⟩
      · have hpositive : 0 < remaining := Nat.pos_of_ne_zero hremaining
        rcases listSortScan_step_correct (fuel := nextFuel) (reverse := reverse)
            horder inv hpositive with
          ⟨consumed, nextState, hstep⟩
        have hnextFuel : remaining - consumed ≤ nextFuel := by
          have hconsumedPositive := hstep.consumedPositive
          have hconsumedWithin := hstep.consumedWithin
          omega
        rcases ih hstep.nextInvariant hnextFuel with
          ⟨terminal, collapsed, result, hrest⟩
        refine ⟨terminal, collapsed, result, ?_⟩
        exact
          { terminalInvariant := hrest.terminalInvariant
            collapseCorrectness := hrest.collapseCorrectness
            collapseResultEq := hrest.collapseResultEq
            preFinishEquation := hstep.scanEquation.trans hrest.preFinishEquation
            resultEq := hstep.scanEquation.trans hrest.resultEq
            finishResultEq := hrest.finishResultEq
            returnCode := hrest.returnCode
            resultFuel := hrest.resultFuel
            finalRun := hrest.finalRun
            collapsedSnapshot := hrest.collapsedSnapshot }

/-- Forward mode performs no final reversal, so the successful result is exactly
the collapsed state with temporary storage released.  This cleanup corollary is
kept separate from the reverse-agnostic principal theorem. -/
theorem listSortScan_forward_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {source : SortSlice alpha nu} {hasKeyfunc : Bool}
    {inputSize fuel : Nat}
    {state : MergeState (Occurrence alpha) nu}
    {lo scanned remaining : Nat}
    (inv : ListSortScanCorrectnessInvariant lt source hasKeyfunc inputSize state
      lo scanned remaining)
    (hFuel : remaining ≤ fuel) :
    ∃ terminal collapsed result,
      ListSortScanCollapseCorrectnessPost lt source hasKeyfunc inputSize fuel
          state lo scanned remaining false terminal collapsed result ∧
        result.state = mergeFreemem collapsed.state ∧
        EntrySnapshotPermutation source result.state.data := by
  rcases listSortScan_complete_correct (reverse := false) horder inv hFuel with
    ⟨terminal, collapsed, result, hpost⟩
  have hfinished :
      result =
        { state := mergeFreemem collapsed.state
          returnCode := 0
          fuelExhausted := false } := by
    have h := hpost.finishResultEq
    simp [finishListSort?] at h
    exact h.symm
  have hsnapshot : EntrySnapshotPermutation source result.state.data := by
    rw [hfinished]
    change EntrySnapshotPermutation source (mergeFreemem collapsed.state).data
    unfold mergeFreemem
    split <;> exact hpost.collapsedSnapshot
  refine ⟨terminal, collapsed, result, hpost, ?_, hsnapshot⟩
  simp [hfinished]

end CPythonListsort

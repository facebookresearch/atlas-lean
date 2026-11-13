/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.OriginRelabelScan
import Code.Correctness.ReverseModeAlgebra

/-!
# Reverse-oriented complete-scan transport

The ordinary whole-scan theorem applies to a canonically tagged reversed
source.  The actual reverse-mode scan instead carries the original occurrence
tags through the initial physical reversal.  These two states differ only by
the total origin mirror, so raw evaluator equivariance transports the complete
scan/collapse certificate without retagging an executed result.

This module deliberately stops before assigning semantic meaning to the final
whole-array reversal.  It retains the exact `finishListSort?` equation and the
mirrored collapsed state; `ReverseModeCorrectness` consumes those facts.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Initial state for the ordinary correctness theorem on the canonically
tagged, physically reversed source. -/
def canonicalReverseScanState (lt : BoolComparator alpha)
    (input : ListSortInput alpha nu) : MergeState (Occurrence alpha) nu :=
  (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
    input.reverseEntries.withOccurrenceKeys.slice).1

/-- The state seen by the actual reverse-mode scan: the canonical reversed
execution with every carried origin mirrored back to its original index. -/
def actualReverseScanState (lt : BoolComparator alpha)
    (input : ListSortInput alpha nu) : MergeState (Occurrence alpha) nu :=
  mirrorMergeState input.slice.entries.size
    (canonicalReverseScanState lt input)

/-- The actual scan starts with the exact paired-entry reversal of the
original occurrence-tagged input.  Keys are not retagged after reversal. -/
theorem actualReverseScanState_data (lt : BoolComparator alpha)
    (input : ListSortInput alpha nu) :
    (actualReverseScanState lt input).data =
      input.withOccurrenceKeys.slice.reverseEntries := by
  change
    mirrorSortSlice input.slice.entries.size
        input.reverseEntries.withOccurrenceKeys.slice =
      input.withOccurrenceKeys.slice.reverseEntries
  exact input.mirror_withOccurrenceKeys_reverseEntries

/-- Full-state initialization bridge for the top-level reverse branch.  Apart
from replacing `data` by the exact paired-entry reversal, every initialized
field—including the fresh inline temporary cells—is the original initialized
field. -/
theorem actualReverseScanState_eq_initial_with_reversed_data
    (lt : BoolComparator alpha) (input : ListSortInput alpha nu) :
    actualReverseScanState lt input =
      { (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
          input.withOccurrenceKeys.slice).1 with
        data := input.withOccurrenceKeys.slice.reverseEntries } := by
  have hsize :
      input.reverseEntries.withOccurrenceKeys.slice.entries.size =
        input.withOccurrenceKeys.slice.entries.size := by
    simp [ListSortInput.withOccurrenceKeys]
  simp [actualReverseScanState, canonicalReverseScanState, initialMergeState,
    mirrorMergeState, mirrorTempStorage, mergeInitTemp,
    ListSortInput.mirror_withOccurrenceKeys_reverseEntries, hsize]

@[simp]
theorem canonicalReverseScanState_comparator (lt : BoolComparator alpha)
    (input : ListSortInput alpha nu) :
    (canonicalReverseScanState lt input).key_compare =
      occurrenceComparator lt := by
  simp [canonicalReverseScanState, initialMergeState]

@[simp]
theorem actualReverseScanState_comparator (lt : BoolComparator alpha)
    (input : ListSortInput alpha nu) :
    (actualReverseScanState lt input).key_compare =
      occurrenceComparator lt := by
  simp [actualReverseScanState]

/-- Complete reverse-oriented scan packet.

`canonical*` are witnesses from the ordinary theorem on the canonically tagged
reversed source.  `terminal`, `collapsed`, and `result` are their exact
origin-mirrored counterparts for the actual reverse-mode scan.  The semantic
facts intentionally stop at `collapsed.state`, before `finishListSort?`
performs the final reversal. -/
structure ReverseScanTransportPost
    (lt : BoolComparator alpha) (input : ListSortInput alpha nu)
    (canonicalTerminal : MergeState (Occurrence alpha) nu)
    (canonicalCollapsed : MergeForceCollapseResult (Occurrence alpha) nu)
    (canonicalResult : ListSortImplResult (Occurrence alpha) nu)
    (terminal : MergeState (Occurrence alpha) nu)
    (collapsed : MergeForceCollapseResult (Occurrence alpha) nu)
    (result : ListSortImplResult (Occurrence alpha) nu) : Prop where
  canonicalPost : ListSortScanCollapseCorrectnessPost lt input.reverseEntries.slice
    input.hasKeyfunc input.slice.entries.size input.slice.entries.size
    (canonicalReverseScanState lt input) 0 0 input.slice.entries.size true
    canonicalTerminal canonicalCollapsed canonicalResult
  terminalMirror : terminal =
    mirrorMergeState input.slice.entries.size canonicalTerminal
  collapsedMirror : collapsed =
    mirrorMergeForceCollapseResult input.slice.entries.size canonicalCollapsed
  resultMirror : result =
    mirrorListSortImplResult input.slice.entries.size canonicalResult
  scanCommutation :
    listSortScan? input.slice.entries.size (actualReverseScanState lt input) 0
        input.slice.entries.size true input.slice.entries.size =
      (listSortScan? input.slice.entries.size
        (canonicalReverseScanState lt input) 0 input.slice.entries.size true
        input.slice.entries.size).map
          (mirrorListSortImplResult input.slice.entries.size)
  collapseResultEq : mergeForceCollapse? terminal = some collapsed
  preFinishEquation :
    listSortScan? input.slice.entries.size (actualReverseScanState lt input) 0
        input.slice.entries.size true input.slice.entries.size =
      finishListSort? collapsed.state true input.slice.entries.size 0 false
  resultEq :
    listSortScan? input.slice.entries.size (actualReverseScanState lt input) 0
        input.slice.entries.size true input.slice.entries.size = some result
  finishResultEq :
    finishListSort? collapsed.state true input.slice.entries.size 0 false =
      some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  preFinishSorted : Sorted (occurrenceComparator lt)
    (collapsed.state.data.entries.map SortSliceEntry.key)
  preFinishReverseStable : ReverseStableOccurrencePermutation lt
    (tagOccurrences (input.slice.entries.map SortSliceEntry.key)).toList
    (collapsed.state.data.entries.map SortSliceEntry.key).toList
  preFinishSnapshot : EntrySnapshotPermutation input.slice collapsed.state.data

/-- Run the complete correctness theorem on the canonical reversed input and
transport that exact execution to the actual reverse-mode occurrence labels.

The premises are exactly the validated input, the order law required by
functional correctness, and the size bounds of the nontrivial top-level scan
branch. -/
theorem reverseScanTransport_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (input : ListSortInput alpha nu)
    (hLower : 2 ≤ input.slice.entries.size)
    (hMax : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ canonicalTerminal canonicalCollapsed canonicalResult
        terminal collapsed result,
      ReverseScanTransportPost lt input canonicalTerminal canonicalCollapsed
        canonicalResult terminal collapsed result := by
  have hLowerReversed : 2 ≤ input.reverseEntries.slice.entries.size := by
    simpa using hLower
  have hMaxReversed :
      input.reverseEntries.slice.entries.size ≤ PY_LIST_MAX := by
    simpa using hMax
  have hinvariant :
      ListSortScanCorrectnessInvariant lt input.reverseEntries.slice
        input.hasKeyfunc input.slice.entries.size
        (canonicalReverseScanState lt input) 0 0 input.slice.entries.size := by
    simpa [canonicalReverseScanState] using
      listSortScanCorrectnessInvariant_initial lt input.reverseEntries
        hLowerReversed hMaxReversed
  rcases listSortScan_complete_correct (reverse := true) horder hinvariant
      (show input.slice.entries.size ≤ input.slice.entries.size from le_rfl) with
    ⟨canonicalTerminal, canonicalCollapsed, canonicalResult, hcanonical⟩
  let size := input.slice.entries.size
  let terminal := mirrorMergeState size canonicalTerminal
  let collapsed := mirrorMergeForceCollapseResult size canonicalCollapsed
  let result := mirrorListSortImplResult size canonicalResult
  have hcommutation :
      listSortScan? size (actualReverseScanState lt input) 0 size true size =
        (listSortScan? size (canonicalReverseScanState lt input) 0 size true
          size).map (mirrorListSortImplResult size) := by
    exact mirrorListSortScan lt size size (canonicalReverseScanState lt input)
      0 size true size (canonicalReverseScanState_comparator lt input)
  have hterminalCompare :
      canonicalTerminal.key_compare = occurrenceComparator lt :=
    hcanonical.terminalInvariant.safety.comparator
  have hcollapse : mergeForceCollapse? terminal = some collapsed := by
    dsimp [terminal, collapsed]
    rw [mirrorMergeForceCollapse lt size canonicalTerminal hterminalCompare,
      hcanonical.collapseResultEq]
    rfl
  have hpreFinish :
      listSortScan? size (actualReverseScanState lt input) 0 size true size =
        finishListSort? collapsed.state true size 0 false := by
    calc
      listSortScan? size (actualReverseScanState lt input) 0 size true size =
          (listSortScan? size (canonicalReverseScanState lt input) 0 size true
            size).map (mirrorListSortImplResult size) := hcommutation
      _ = (finishListSort? canonicalCollapsed.state true size 0 false).map
            (mirrorListSortImplResult size) := by
          rw [hcanonical.preFinishEquation]
      _ = finishListSort? collapsed.state true size 0 false := by
          dsimp [collapsed]
          exact (mirrorFinishListSort size canonicalCollapsed.state true size
            0 false).symm
  have hresultEq :
      listSortScan? size (actualReverseScanState lt input) 0 size true size =
        some result := by
    rw [hcommutation, hcanonical.resultEq]
    rfl
  have hfinishResult :
      finishListSort? collapsed.state true size 0 false = some result :=
    hpreFinish.symm.trans hresultEq
  have hwhole := hcanonical.wholeDataCorrect
  have hcanonicalKeys :
      input.reverseEntries.slice.entries.map SortSliceEntry.key =
        (input.slice.entries.map SortSliceEntry.key).reverse := by
    simp [SortSlice.reverseEntries, Array.map_reverse]
  have hcanonicalStable : StableOccurrencePermutation lt
      (tagOccurrences
        (input.slice.entries.map SortSliceEntry.key).reverse).toList
      (canonicalCollapsed.state.data.entries.map SortSliceEntry.key).toList := by
    rw [← hcanonicalKeys]
    exact hwhole.2
  have hactualKeys :
      collapsed.state.data.entries.map SortSliceEntry.key =
        (canonicalCollapsed.state.data.entries.map SortSliceEntry.key).map
          (mirrorOccurrence size) := by
    dsimp [collapsed]
    simp [Array.map_map, Function.comp_def]
  have hsorted : Sorted (occurrenceComparator lt)
      (collapsed.state.data.entries.map SortSliceEntry.key) := by
    rw [hactualKeys]
    exact (sorted_mirror_iff lt size _).2 hwhole.1
  have hstable : ReverseStableOccurrencePermutation lt
      (tagOccurrences (input.slice.entries.map SortSliceEntry.key)).toList
      (collapsed.state.data.entries.map SortSliceEntry.key).toList := by
    rw [hactualKeys, Array.toList_map]
    simpa [size] using stable_reversedSource_mirror hcanonicalStable
  have hcanonicalSnapshot : EntrySnapshotPermutation
      input.slice.reverseEntries canonicalCollapsed.state.data := by
    simpa using hcanonical.collapsedSnapshot
  have hsnapshot :
      EntrySnapshotPermutation input.slice collapsed.state.data := by
    dsimp [collapsed]
    exact hcanonicalSnapshot.mirror_reversedSource
  refine ⟨canonicalTerminal, canonicalCollapsed, canonicalResult,
    terminal, collapsed, result, ?_⟩
  exact
    { canonicalPost := hcanonical
      terminalMirror := rfl
      collapsedMirror := rfl
      resultMirror := rfl
      scanCommutation := hcommutation
      collapseResultEq := hcollapse
      preFinishEquation := hpreFinish
      resultEq := hresultEq
      finishResultEq := hfinishResult
      returnCode := by
        dsimp [result, mirrorListSortImplResult]
        exact hcanonical.returnCode
      resultFuel := by
        dsimp [result, mirrorListSortImplResult]
        exact hcanonical.resultFuel
      preFinishSorted := hsorted
      preFinishReverseStable := hstable
      preFinishSnapshot := hsnapshot }

end CPythonListsort

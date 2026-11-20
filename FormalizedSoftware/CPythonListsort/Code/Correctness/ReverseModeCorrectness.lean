/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.ReverseScanTransport

/-!
# Correctness of CPython's reverse-mode pattern

The reverse-oriented scan transport supplies the actual pre-finish state:
sorted by the forward comparator, but reverse-stable in the original origin
labels.  This module proves that the transcribed final whole-slice reversal
turns that state into a sorted, stable result for the swapped comparator while
preserving every key/payload pair.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- The occurrence keys physically retained in a completed modeled result. -/
def ListSortImplResult.occurrences
    (result : ListSortImplResult (Occurrence alpha) nu) :
    Array (Occurrence alpha) :=
  result.state.data.entries.map SortSliceEntry.key

/-- Public semantic packet for the nontrivial `reverse = true` scan branch. -/
structure ReverseModeCorrectnessPost
    (lt : BoolComparator alpha) (input : ListSortInput alpha nu)
    (result : ListSortImplResult (Occurrence alpha) nu) : Prop where
  scanResultEq :
    listSortScan? input.slice.entries.size (actualReverseScanState lt input) 0
      input.slice.entries.size true input.slice.entries.size = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  sorted : Sorted (occurrenceComparator (swappedComparator lt))
    result.occurrences
  stable : StableOccurrencePermutation (swappedComparator lt)
    (tagOccurrences
      (input.slice.entries.map SortSliceEntry.key)).toList
    result.occurrences.toList
  entrySnapshot : EntrySnapshotPermutation input.slice result.state.data

/-- The actual final reversal in `finishListSort?` realizes the mathematical
reverse-mode contract for every validated nontrivial input. -/
theorem reverseMode_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (input : ListSortInput alpha nu)
    (hLower : 2 ≤ input.slice.entries.size)
    (hMax : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ReverseModeCorrectnessPost lt input result := by
  rcases reverseScanTransport_correct lt horder input hLower hMax with
    ⟨canonicalTerminal, canonicalCollapsed, canonicalResult,
      terminal, collapsed, result, htransport⟩
  have hExtent :
      collapsed.state.data.entries.size = input.slice.entries.size := by
    have hlength := htransport.preFinishSnapshot.length_eq
    simpa [EntrySnapshotPermutation, tagSortSliceOccurrences] using hlength
  have hRange : SortSlice.RangeInBounds collapsed.state.data 0
      input.slice.entries.size := by
    constructor
    · omega
    · simp [hExtent]
  rcases sortsliceReverse_correct collapsed.state.data 0
      input.slice.entries.size hRange with
    ⟨reversed, hreversed, hreversedFuel, hreversedEntries⟩
  have hReversedEntries :
      reversed.slice.entries = collapsed.state.data.entries.reverse := by
    rw [hreversedEntries]
    apply Array.ext <;>
      simp [ReverseRangeSpec.reverseRangeEntries, hExtent]
  let updated : MergeState (Occurrence alpha) nu :=
    { collapsed.state with data := reversed.slice }
  have hFinalReverse : 1 < input.slice.entries.size := by omega
  have hResult : result =
      { state := mergeFreemem updated
        returnCode := 0
        fuelExhausted := false } := by
    have hfinish := htransport.finishResultEq
    simp [finishListSort?, hFinalReverse, hreversed, hreversedFuel]
      at hfinish
    exact hfinish.symm
  have hResultData : result.state.data = reversed.slice := by
    rw [hResult]
    change (mergeFreemem updated).data = reversed.slice
    unfold mergeFreemem
    split <;> rfl
  have hResultOccurrences :
      result.occurrences =
        (collapsed.state.data.entries.map SortSliceEntry.key).reverse := by
    rw [ListSortImplResult.occurrences, hResultData, hReversedEntries,
      Array.map_reverse]
  have hSnapshotReversed :
      EntrySnapshotPermutation input.slice reversed.slice := by
    apply htransport.preFinishSnapshot.preserve_of_whole_entries_perm
    rw [hReversedEntries, Array.toList_reverse]
    exact List.reverse_perm _
  refine ⟨result, ?_⟩
  exact
    { scanResultEq := htransport.resultEq
      returnCode := htransport.returnCode
      resultFuel := htransport.resultFuel
      sorted := by
        rw [hResultOccurrences]
        simpa only [occurrenceComparator_swapped] using
          htransport.preFinishSorted.reverse_swapped
      stable := by
        rw [hResultOccurrences, Array.toList_reverse]
        exact htransport.preFinishReverseStable.reverse
      entrySnapshot := by
        rw [hResultData]
        exact hSnapshotReversed }

end CPythonListsort

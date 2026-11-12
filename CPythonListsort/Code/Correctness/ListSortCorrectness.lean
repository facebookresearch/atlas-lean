/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.ScanLoopCorrectness
import Code.Correctness.ReverseModeCorrectness
import Code.Correctness.OccurrenceErasureScan

/-!
# Public functional correctness of listsort

This module packages correctness at the proof-carrying `ListSortInput`
boundary.  The implementation sorts occurrence-tagged keys so origins travel
through every modeled movement; the final post exposes requested-order
sortedness, occurrence-level stability, and the whole key/payload snapshot.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- The complete implementation-level functional-correctness certificate.

`rawResultEq` is deliberately part of the public post: the semantic facts are
about the result returned by the transcribed evaluator, not an independently
constructed sorted array.  `entrySnapshot` retains keyed payload pairing in
addition to the key-facing sortedness and stability clauses. -/
structure ListSortCorrectnessPost
    (lt : BoolComparator alpha) (reverse : Bool)
    (input : ListSortInput alpha nu)
    (result : ListSortImplResult (Occurrence alpha) nu) : Prop where
  rawResultEq :
    listSort? (occurrenceComparator lt) reverse input.withOccurrenceKeys =
      some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  sorted :
    Sorted (occurrenceComparator (requestedComparator lt reverse))
      result.occurrences
  stable :
    StableOccurrencePermutation (requestedComparator lt reverse)
      (tagOccurrences
        (input.slice.entries.map SortSliceEntry.key)).toList
      result.occurrences.toList
  entrySnapshot : EntrySnapshotPermutation input.slice result.state.data

/-- The occurrence execution carried by a correctness post erases to the
ordinary untagged execution on the same validated input. -/
theorem ListSortCorrectnessPost.untaggedResultEq
    {lt : BoolComparator alpha} {reverse : Bool}
    {input : ListSortInput alpha nu}
    {result : ListSortImplResult (Occurrence alpha) nu}
    (post : ListSortCorrectnessPost lt reverse input result) :
    listSort? lt reverse input =
      some (eraseOccurrenceListSortImplResult result) := by
  rw [eraseOccurrenceListSort, post.rawResultEq]
  rfl

/-- Canonically tagged input keys are stable relative to themselves for every
comparator, without any ordering-law premise. -/
theorem stableOccurrencePermutation_tagOccurrences_refl
    (lt : BoolComparator alpha) (xs : Array alpha) :
    StableOccurrencePermutation lt (tagOccurrences xs).toList
      (tagOccurrences xs).toList := by
  have hextract :
      (tagOccurrences xs).extract 0 xs.size = tagOccurrences xs := by
    apply Array.extract_eq_self_of_le
    simp [tagOccurrences]
  simpa [canonicalOccurrenceSegment, hextract] using
    canonicalOccurrenceSegment_countRunCanonical lt xs 0 xs.size

/-- Any array of length at most one is sorted under an arbitrary Boolean
comparator. -/
theorem sorted_of_size_lt_two
    (lt : BoolComparator alpha) (xs : Array alpha) (hsize : xs.size < 2) :
    Sorted lt xs := by
  unfold Sorted
  have hlist : xs.toList.length < 2 := by simpa using hsize
  generalize hxs : xs.toList = values at hlist ⊢
  cases values with
  | nil => simp
  | cons value tail =>
      cases tail with
      | nil => simp
      | cons next rest => simp at hlist

/-- Inputs of length zero or one bypass the scan, but still return the exact
tagged input snapshot and satisfy the full correctness post in either mode. -/
theorem listSort_small_correct
    (lt : BoolComparator alpha) (reverse : Bool)
    (input : ListSortInput alpha nu)
    (hsize : input.slice.entries.size < 2)
    (hmax : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ListSortCorrectnessPost lt reverse input result := by
  let tagged := input.withOccurrenceKeys
  let state :=
    (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
      tagged.slice).1
  let result : ListSortImplResult (Occurrence alpha) nu :=
    { state := mergeFreemem state
      returnCode := 0
      fuelExhausted := false }
  have hstopped :
      (initialMergeState (occurrenceComparator lt) tagged.hasKeyfunc
        tagged.slice).2 = true := by
    exact (initialMergeState_package (occurrenceComparator lt)
      tagged.hasKeyfunc tagged.slice
      (by simpa [tagged, ListSortInput.withOccurrenceKeys] using hmax)
      tagged.valuesMode).minrunStopped
  have htaggedMax : tagged.slice.entries.size ≤ PY_LIST_MAX := by
    simpa [tagged, ListSortInput.withOccurrenceKeys] using hmax
  have htaggedSmall : tagged.slice.entries.size < 2 := by
    simpa [tagged, ListSortInput.withOccurrenceKeys] using hsize
  have hpublicTaggedMax :
      input.withOccurrenceKeys.slice.entries.size ≤ PY_LIST_MAX := by
    simpa [tagged] using htaggedMax
  have hpublicTaggedSmall :
      input.withOccurrenceKeys.slice.entries.size < 2 := by
    simpa [tagged] using htaggedSmall
  have hpublicStopped :
      (initialMergeState (occurrenceComparator lt)
        input.withOccurrenceKeys.hasKeyfunc
        input.withOccurrenceKeys.slice).2 = true := by
    simpa [tagged] using hstopped
  have hstoppedLiteral :
      (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
        (tagSortSliceOccurrences input.slice)).2 = true := by
    simpa [tagged, ListSortInput.withOccurrenceKeys] using hstopped
  have hnoFinalReverse : ¬1 < tagged.slice.entries.size := by omega
  have hsmallLe : input.slice.entries.size ≤ 1 := by omega
  have hdata : result.state.data = tagged.slice := by
    change (mergeFreemem state).data = tagged.slice
    have hframe := mergeFreemem_frame state
      ((initialMergeState_package (occurrenceComparator lt)
        input.hasKeyfunc tagged.slice
        (by simpa [tagged, ListSortInput.withOccurrenceKeys] using hmax)
        tagged.valuesMode).tempInvariant)
    exact hframe.2.2.1.trans (by simp [state])
  have hoccurrences :
      result.occurrences =
        tagOccurrences (input.slice.entries.map SortSliceEntry.key) := by
    rw [ListSortImplResult.occurrences, hdata]
    apply Array.ext <;>
      simp [tagged, ListSortInput.withOccurrenceKeys,
        tagSortSliceOccurrences, tagOccurrences]
  refine ⟨result, ?_⟩
  refine
    { rawResultEq := ?_
      returnCode := rfl
      resultFuel := rfl
      sorted := ?_
      stable := ?_
      entrySnapshot := ?_ }
  · have hfinish :
        finishListSort? state reverse tagged.slice.entries.size 0 false =
          some result := by
      simp [finishListSort?, hnoFinalReverse, result]
    simpa [listSort?, listSortImpl?, hpublicTaggedMax, hpublicStopped,
      hpublicTaggedSmall, hmax, hstopped, hstoppedLiteral, hsmallLe, tagged, state,
      ListSortInput.withOccurrenceKeys]
      using hfinish
  · rw [hoccurrences]
    apply sorted_of_size_lt_two
    simpa [tagOccurrences] using hsize
  · rw [hoccurrences]
    exact stableOccurrencePermutation_tagOccurrences_refl _ _
  · rw [hdata]
    exact EntrySnapshotPermutation.with_occurrence_keys input

/-- Forward mode composes initialization, the complete scan/collapse theorem,
and cleanup without adding any premise beyond the signed input, size, and
strict-weak-order contract. -/
theorem listSort_forward_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (input : ListSortInput alpha nu)
    (hmax : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ListSortCorrectnessPost lt false input result := by
  by_cases hsmall : input.slice.entries.size < 2
  · exact listSort_small_correct lt false input hsmall hmax
  · have hlower : 2 ≤ input.slice.entries.size := by omega
    let tagged := input.withOccurrenceKeys
    let state :=
      (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
        tagged.slice).1
    have hinitial := listSortScanCorrectnessInvariant_initial lt input hlower hmax
    rcases listSortScan_forward_correct horder hinitial (Nat.le_refl _) with
      ⟨terminal, collapsed, result, hscan, hstate, hsnapshot⟩
    have hwhole :=
      ListSortScanCollapseCorrectnessPost.wholeDataCorrect hscan
    have hresultOccurrences :
        result.occurrences =
          collapsed.state.data.entries.map SortSliceEntry.key := by
      rw [ListSortImplResult.occurrences, hstate]
      have hframe := mergeFreemem_frame collapsed.state
        hscan.collapseCorrectness.safety.tempInvariant
      rw [hframe.2.2.1]
    have hstopped :
        (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
          tagged.slice).2 = true := by
      exact (initialMergeState_package (occurrenceComparator lt)
        input.hasKeyfunc tagged.slice
        (by simpa [tagged, ListSortInput.withOccurrenceKeys] using hmax)
        tagged.valuesMode).minrunStopped
    have hpublicTaggedMax :
        input.withOccurrenceKeys.slice.entries.size ≤ PY_LIST_MAX := by
      simpa [tagged, ListSortInput.withOccurrenceKeys] using hmax
    have hpublicNotSmall :
        ¬input.withOccurrenceKeys.slice.entries.size < 2 := by
      simpa [tagged, ListSortInput.withOccurrenceKeys] using hsmall
    have hpublicStopped :
        (initialMergeState (occurrenceComparator lt)
        input.withOccurrenceKeys.hasKeyfunc
        input.withOccurrenceKeys.slice).2 = true := by
      simpa [tagged, ListSortInput.withOccurrenceKeys] using hstopped
    have hstoppedLiteral :
        (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
          (tagSortSliceOccurrences input.slice)).2 = true := by
      simpa [tagged, ListSortInput.withOccurrenceKeys] using hstopped
    have hnotSmallLe : ¬input.slice.entries.size ≤ 1 := by omega
    refine ⟨result, ?_⟩
    refine
      { rawResultEq := ?_
        returnCode := hscan.returnCode
        resultFuel := hscan.resultFuel
        sorted := ?_
        stable := ?_
        entrySnapshot := hsnapshot }
    · simpa [listSort?, listSortImpl?, hpublicTaggedMax, hpublicStopped,
        hpublicNotSmall, hmax, hstopped, hstoppedLiteral, hnotSmallLe, tagged, state,
        ListSortInput.withOccurrenceKeys]
        using hscan.resultEq
    · simpa [hresultOccurrences] using hwhole.1
    · simpa [hresultOccurrences] using hwhole.2

/-- Reverse mode uses the actual initial paired-entry reversal, the
reverse-oriented scan theorem, and the actual final reversal. -/
theorem listSort_reverse_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (input : ListSortInput alpha nu)
    (hmax : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ListSortCorrectnessPost lt true input result := by
  by_cases hsmall : input.slice.entries.size < 2
  · exact listSort_small_correct lt true input hsmall hmax
  · have hlower : 2 ≤ input.slice.entries.size := by omega
    rcases reverseMode_correct lt horder input hlower hmax with
      ⟨result, hreverse⟩
    let tagged := input.withOccurrenceKeys
    let state :=
      (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
        tagged.slice).1
    have htaggedMax : tagged.slice.entries.size ≤ PY_LIST_MAX := by
      simpa [tagged, ListSortInput.withOccurrenceKeys] using hmax
    have hstopped :
        (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
          tagged.slice).2 = true := by
      exact (initialMergeState_package (occurrenceComparator lt)
        input.hasKeyfunc tagged.slice htaggedMax tagged.valuesMode).minrunStopped
    have hRange : SortSlice.RangeInBounds state.data 0
        input.slice.entries.size := by
      constructor
      · omega
      · simp [state, tagged, ListSortInput.withOccurrenceKeys]
    rcases sortsliceReverse_correct state.data 0 input.slice.entries.size
        hRange with
      ⟨reversed, hreversed, hreversedFuel, hreversedEntries⟩
    have hReversedSlice :
        reversed.slice = tagged.slice.reverseEntries := by
      apply congrArg SortSlice.mk
      rw [hreversedEntries]
      apply Array.ext <;>
        simp [state, tagged, ListSortInput.withOccurrenceKeys,
          ReverseRangeSpec.reverseRangeEntries]
    have hScanState :
        { state with data := reversed.slice } =
          actualReverseScanState lt input := by
      rw [hReversedSlice]
      simpa [state, tagged, ListSortInput.withOccurrenceKeys] using
        (actualReverseScanState_eq_initial_with_reversed_data lt input).symm
    have hpublicReverse :
        sortsliceReverse? input.withOccurrenceKeys.slice 0
            input.withOccurrenceKeys.slice.entries.size = some reversed := by
      simpa [state, tagged, ListSortInput.withOccurrenceKeys] using hreversed
    have hpublicReverseFuel : reversed.fuelExhausted = false :=
      hreversedFuel
    have hpublicScanState :
        { (initialMergeState (occurrenceComparator lt)
            input.withOccurrenceKeys.hasKeyfunc
            input.withOccurrenceKeys.slice).1 with
          data := reversed.slice } = actualReverseScanState lt input := by
      simpa [state, tagged, ListSortInput.withOccurrenceKeys] using hScanState
    have hpublicTaggedMax :
        input.withOccurrenceKeys.slice.entries.size ≤ PY_LIST_MAX := by
      simpa [tagged] using htaggedMax
    have hpublicNotSmall :
        ¬input.withOccurrenceKeys.slice.entries.size < 2 := by
      simpa [tagged, ListSortInput.withOccurrenceKeys] using hsmall
    have hpublicStopped :
        (initialMergeState (occurrenceComparator lt)
          input.withOccurrenceKeys.hasKeyfunc
          input.withOccurrenceKeys.slice).2 = true := by
      simpa [tagged, ListSortInput.withOccurrenceKeys] using hstopped
    refine ⟨result, ?_⟩
    exact
      { rawResultEq := by
          change listSortImpl? (occurrenceComparator lt) true
            input.withOccurrenceKeys.hasKeyfunc input.withOccurrenceKeys.slice =
              some result
          unfold listSortImpl?
          rw [if_pos hpublicTaggedMax]
          simp only [hpublicStopped, Bool.not_true, Bool.false_eq_true,
            if_false]
          rw [if_neg hpublicNotSmall]
          simp only [if_true]
          rw [initialMergeState_data]
          rw [hpublicReverse]
          simp only [hpublicReverseFuel, Bool.false_eq_true, if_false]
          rw [hpublicScanState]
          simpa [ListSortInput.withOccurrenceKeys] using hreverse.scanResultEq
        returnCode := hreverse.returnCode
        resultFuel := hreverse.resultFuel
        sorted := by simpa [requestedComparator] using hreverse.sorted
        stable := by simpa [requestedComparator] using hreverse.stable
        entrySnapshot := hreverse.entrySnapshot }

/-- The validated implementation-level theorem for either public direction. -/
theorem listSort_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (reverse : Bool) (input : ListSortInput alpha nu)
    (hmax : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ListSortCorrectnessPost lt reverse input result := by
  cases reverse
  · exact listSort_forward_correct lt horder input hmax
  · exact listSort_reverse_correct lt horder input hmax

/-- Keyed-array specialization of `listSort_correct`.  The returned
`ListSortCorrectnessPost` exposes requested-order key sortedness,
occurrence-level stability, and permutation of complete key/payload entries.
The first conjunct connects that certificate to the ordinary untagged public
evaluator on the same keyed input. -/
theorem listsort_correct_keyed
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (reverse : Bool) (entries : Array (alpha × nu))
    (hmax : entries.size ≤ PY_LIST_MAX) :
    ∃ result : ListSortImplResult (Occurrence alpha) nu,
      listSort? lt reverse (ListSortInput.keyed entries) =
          some (eraseOccurrenceListSortImplResult result) ∧
        ListSortCorrectnessPost lt reverse
          (ListSortInput.keyed entries) result := by
  have hinputSize :
      (ListSortInput.keyed entries).slice.entries.size ≤ PY_LIST_MAX := by
    simpa [ListSortInput.keyed] using hmax
  rcases listSort_correct lt horder reverse (ListSortInput.keyed entries)
      hinputSize with
    ⟨result, hresult⟩
  exact ⟨result, hresult.untaggedResultEq, hresult⟩

/-- Required ordinary-array corollary.  The first equation exposes the actual
untagged evaluator result; the second exposes the occurrence-enriched
execution whose carried origins witness stability.  Exact erasure connects
the two, so origins are neither inspected by execution nor manufactured after
sorting. -/
theorem listsort_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (reverse : Bool) (xs : Array alpha)
    (hmax : xs.size ≤ PY_LIST_MAX) :
    ∃ result : ListSortImplResult (Occurrence alpha) PUnit,
      listSort? lt reverse (ListSortInput.unkeyed xs) =
          some (eraseOccurrenceListSortImplResult result) ∧
        listSort? (occurrenceComparator lt) reverse
            (ListSortInput.unkeyed xs).withOccurrenceKeys = some result ∧
        let tagged : TaggedOutput alpha := ⟨result.occurrences⟩
        Sorted (requestedComparator lt reverse) tagged.values ∧
          Stable (requestedComparator lt reverse) xs tagged ∧
          tagged.values.toList.Perm xs.toList := by
  have hinputSize :
      (ListSortInput.unkeyed xs).slice.entries.size ≤ PY_LIST_MAX := by
    simpa [ListSortInput.unkeyed, ListSortInput.unkeyedAs] using hmax
  rcases listSort_correct lt horder reverse (ListSortInput.unkeyed xs)
      hinputSize with
    ⟨result, hresult⟩
  let tagged : TaggedOutput alpha := ⟨result.occurrences⟩
  have hunkeyedKeys :
      (ListSortInput.unkeyed xs).slice.entries.map SortSliceEntry.key = xs := by
    apply Array.ext <;>
      simp [ListSortInput.unkeyed, ListSortInput.unkeyedAs]
  have hsorted :
      Sorted (requestedComparator lt reverse) tagged.values := by
    simpa [tagged, TaggedOutput.values] using hresult.sorted.values
  have hoccurrenceStable : StableOccurrencePermutation
      (requestedComparator lt reverse) (tagOccurrences xs).toList
      result.occurrences.toList := by
    have hstable := hresult.stable
    rw [hunkeyedKeys] at hstable
    exact hstable
  have hstable : Stable (requestedComparator lt reverse) xs tagged := by
    simpa [Stable, tagged] using hoccurrenceStable
  exact ⟨result, hresult.untaggedResultEq, hresult.rawResultEq, hsorted,
    hstable, hstable.values_perm⟩

/-! ## Inhabited boundary witnesses -/

private def correctnessRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private theorem correctnessRegressionOrder :
    BoolStrictWeakOrder correctnessRegressionLt := by
  constructor
  let hstrict : IsStrictOrder Nat
      (fun left right => correctnessRegressionLt left right = true) :=
    { irrefl := by simp [correctnessRegressionLt]
      trans := by
        intro a b c hab hbc
        simp [correctnessRegressionLt] at hab hbc ⊢
        omega }
  exact @IsStrictWeakOrder.mk Nat
    (fun left right => correctnessRegressionLt left right = true)
    hstrict (by
      intro a b c hab hbc
      simp [correctnessRegressionLt] at hab hbc ⊢
      omega)

private def reverseKeyedDuplicateInput : ListSortInput Nat Nat :=
  ListSortInput.keyed #[(2, 20), (1, 10), (1, 11), (2, 21)]

private structure CorrectnessRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

private def correctnessRegressionView
    (result : ListSortImplResult (Occurrence Nat) Nat) :
    CorrectnessRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    entries := result.state.data.entries.toList.map fun entry =>
      (entry.key.value, entry.key.origin, entry.value) }

/-- Kernel-checked, inhabited keyed reverse-mode boundary witness with
duplicate keys.  The raw-result equation ties every semantic conjunct to the
actual `listSort?` execution.  Sortedness fixes descending key order, the
stable-occurrence predicate keeps equal keys in increasing origin order, and
the entry snapshot keeps each payload paired with its original occurrence.

This deliberately avoids reducing the complete evaluator inside the kernel:
the public correctness theorem supplies the witness and all three observable
postconditions without adding another compiler-checked evaluator leaf. -/
theorem listSort_reverse_keyed_duplicate_regression :
    ∃ result,
      listSort? (occurrenceComparator correctnessRegressionLt) true
          reverseKeyedDuplicateInput.withOccurrenceKeys = some result ∧
        result.returnCode = 0 ∧
        result.fuelExhausted = false ∧
        Sorted
          (occurrenceComparator
            (requestedComparator correctnessRegressionLt true))
          result.occurrences ∧
        StableOccurrencePermutation
          (requestedComparator correctnessRegressionLt true)
          (tagOccurrences
            (reverseKeyedDuplicateInput.slice.entries.map
              SortSliceEntry.key)).toList
          result.occurrences.toList ∧
        EntrySnapshotPermutation reverseKeyedDuplicateInput.slice
          result.state.data := by
  have hmax : reverseKeyedDuplicateInput.slice.entries.size ≤ PY_LIST_MAX := by
    norm_num [reverseKeyedDuplicateInput, ListSortInput.keyed, PY_LIST_MAX,
      PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  rcases listSort_reverse_correct correctnessRegressionLt
      correctnessRegressionOrder reverseKeyedDuplicateInput hmax with
    ⟨result, hresult⟩
  exact ⟨result, hresult.rawResultEq, hresult.returnCode,
    hresult.resultFuel, hresult.sorted, hresult.stable,
    hresult.entrySnapshot⟩

set_option maxRecDepth 100000 in
/-- Empty and singleton executions really take the public bypass, return
successfully in reverse mode, and retain the exact occurrence/payload data. -/
theorem listSort_small_boundary_regression :
    (listSort? (occurrenceComparator correctnessRegressionLt) true
      (ListSortInput.unkeyed (#[] : Array Nat)).withOccurrenceKeys).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.data.entries.size)) = some (0, false, 0) ∧
      (listSort? (occurrenceComparator correctnessRegressionLt) true
        (ListSortInput.keyed #[(7, 70)]).withOccurrenceKeys).map
          correctnessRegressionView =
        some
          { returnCode := 0
            fuelExhausted := false
            entries := [(7, 0, some 70)] } := by
  let emptyInput : ListSortInput Nat PUnit :=
    ListSortInput.unkeyed (#[] : Array Nat)
  let singletonInput : ListSortInput Nat Nat :=
    ListSortInput.keyed #[(7, 70)]
  have hemptySmall : emptyInput.slice.entries.size < 2 := by
    norm_num [emptyInput, ListSortInput.unkeyed, ListSortInput.unkeyedAs]
  have hemptyMax : emptyInput.slice.entries.size ≤ PY_LIST_MAX := by
    norm_num [emptyInput, ListSortInput.unkeyed, ListSortInput.unkeyedAs,
      PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  have hsingletonSmall : singletonInput.slice.entries.size < 2 := by
    norm_num [singletonInput, ListSortInput.keyed]
  have hsingletonMax : singletonInput.slice.entries.size ≤ PY_LIST_MAX := by
    norm_num [singletonInput, ListSortInput.keyed, PY_LIST_MAX,
      PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  rcases listSort_small_correct correctnessRegressionLt true emptyInput
      hemptySmall hemptyMax with ⟨emptyResult, hempty⟩
  rcases listSort_small_correct correctnessRegressionLt true singletonInput
      hsingletonSmall hsingletonMax with ⟨singletonResult, hsingleton⟩
  have hemptyRaw :
      listSort? (occurrenceComparator correctnessRegressionLt) true
          (ListSortInput.unkeyed (#[] : Array Nat)).withOccurrenceKeys =
        some emptyResult := by
    simpa [emptyInput] using hempty.rawResultEq
  have hsingletonRaw :
      listSort? (occurrenceComparator correctnessRegressionLt) true
          (ListSortInput.keyed #[(7, 70)]).withOccurrenceKeys =
        some singletonResult := by
    simpa [singletonInput] using hsingleton.rawResultEq
  have hemptyEntries : emptyResult.state.data.entries = #[] := by
    have hsnapshot := hempty.entrySnapshot
    have hlist : emptyResult.state.data.entries.toList.Perm [] := by
      simpa [EntrySnapshotPermutation, emptyInput, ListSortInput.unkeyed,
        ListSortInput.unkeyedAs, tagSortSliceOccurrences] using hsnapshot
    apply Array.toList_inj.mp
    simpa using hlist.eq_nil
  have hsingletonEntries : singletonResult.state.data.entries =
      #[{ key := { value := 7, origin := 0 }, value := some 70 }] := by
    have hsnapshot := hsingleton.entrySnapshot
    simp [EntrySnapshotPermutation, singletonInput, ListSortInput.keyed,
      tagSortSliceOccurrences] at hsnapshot
    apply Array.toList_inj.mp
    simpa using hsnapshot
  constructor
  · rw [hemptyRaw]
    simp [hempty.returnCode, hempty.resultFuel, hemptyEntries]
  · rw [hsingletonRaw]
    simp [correctnessRegressionView, hsingleton.returnCode,
      hsingleton.resultFuel, hsingletonEntries]

set_option linter.style.nativeDecide false in
/-- Compiler-checked exact-output witness for stable forward sorting with
duplicate keys.  This declaration is review evidence only and is forbidden
from becoming a proof dependency by `verify/verify_trust_boundary.py`. -/
theorem listSort_forward_keyed_duplicate_exact_regression :
    (listSort? (occurrenceComparator correctnessRegressionLt) false
        reverseKeyedDuplicateInput.withOccurrenceKeys).map
        correctnessRegressionView =
      some
        { returnCode := 0
          fuelExhausted := false
          entries :=
            [(1, 1, some 10), (1, 2, some 11),
             (2, 0, some 20), (2, 3, some 21)] } := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Compiler-checked exact-output witness for reverse sorting with duplicate
keys: key order is descending while equal-key origins, and therefore their
payloads, retain original order.  This declaration is review evidence only and
is forbidden from becoming a proof dependency by
`verify/verify_trust_boundary.py`. -/
theorem listSort_reverse_keyed_duplicate_exact_regression :
    (listSort? (occurrenceComparator correctnessRegressionLt) true
        reverseKeyedDuplicateInput.withOccurrenceKeys).map
        correctnessRegressionView =
      some
        { returnCode := 0
          fuelExhausted := false
          entries :=
            [(2, 0, some 20), (2, 3, some 21),
             (1, 1, some 10), (1, 2, some 11)] } := by
  native_decide

end CPythonListsort

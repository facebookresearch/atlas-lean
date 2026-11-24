/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.ScanRemainder

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-- Concrete keyed-input pin: occurrence tagging keeps the payload `42`
paired with key `7` while attaching absolute origin zero. -/
private theorem listSortInput_keyed_occurrence_payload_regression :
    let input := ListSortInput.keyed (#[(7, 42)] : Array (Nat × Nat))
    input.withOccurrenceKeys.hasKeyfunc = true ∧
      input.withOccurrenceKeys.slice.entries =
        #[{ key := { value := 7, origin := 0 }, value := some 42 }] := by
  norm_num [ListSortInput.withOccurrenceKeys, ListSortInput.keyed,
    tagSortSliceOccurrences]

private def scanRemainderRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def scanRemainderRegressionEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

private def scanRemainderRegressionInput : Array Nat :=
  #[1, 2]

/-- Empty pending coverage at `scanned = 0`, but with a deliberately corrupted
first unscanned key. -/
private def scanRemainderWrongSuffixState :
    MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 0
    data :=
      { entries :=
          #[scanRemainderRegressionEntry 99 0,
            scanRemainderRegressionEntry 2 1] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator scanRemainderRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Anti-vacuity regression for the new invariant: the previously approved
pending-run predicate genuinely permits a wrong unscanned suffix, while
`ScanRemainderMatches` rejects that same concrete state. -/
theorem pendingRunsCorrect_allows_wrong_suffix_but_scanRemainder_rejects :
    PendingRunsCorrect scanRemainderRegressionLt
        scanRemainderRegressionInput scanRemainderWrongSuffixState 0 ∧
      ¬ScanRemainderMatches scanRemainderRegressionInput
        scanRemainderWrongSuffixState 0 := by
  constructor
  · norm_num [PendingRunsCorrect, PendingLayout, PendingRunsCover,
      StableOccurrencePermutation, pendingOccurrenceKeys,
      canonicalOccurrenceSegment, scanRemainderRegressionInput,
      scanRemainderWrongSuffixState, PySSize.Nonnegative,
      BitVec.toNat_ofNat, BitVec.msb, BitVec.getMsbD, BitVec.getLsbD]
    all_goals decide
  · intro h
    have hkeys := h.keys_eq
    norm_num [sortSliceRangeKeys, sortSliceRangeEntries,
      canonicalOccurrenceSegment, tagOccurrences,
      scanRemainderRegressionInput, scanRemainderWrongSuffixState,
      scanRemainderRegressionEntry] at hkeys

private def scanRemainderNonzeroBaseInput : Array Nat :=
  #[99, 7, 7, 88]

/-- At absolute base one, the visible values are right but the second `7`
incorrectly reuses origin one.  The prefix at base zero is deliberately
perfect, so a definition that forgot the `basekeys` offset would accept it. -/
private def scanRemainderNonzeroBaseWrongOriginState :
    MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 1
    data :=
      { entries :=
          #[scanRemainderRegressionEntry 99 0,
            scanRemainderRegressionEntry 7 1,
            scanRemainderRegressionEntry 7 1,
            scanRemainderRegressionEntry 88 3] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator scanRemainderRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Nonzero-base/origin regression.  A mistaken zero-based comparison would
match exactly, and the correctly selected range has the right visible values;
nevertheless the invariant rejects it because absolute origin two was changed
to one.  Thus neither the base offset nor origin equality can be erased
silently. -/
theorem scanRemainder_nonzero_base_wrong_origin_rejected :
    (sortSliceRangeKeys scanRemainderNonzeroBaseWrongOriginState.data 0 2).toList =
        canonicalOccurrenceSegment scanRemainderNonzeroBaseInput 0 2 ∧
      ((sortSliceRangeKeys scanRemainderNonzeroBaseWrongOriginState.data 1 2).map
        Occurrence.value).toList =
        (scanRemainderNonzeroBaseInput.extract 1 3).toList ∧
      ¬ScanRemainderMatches scanRemainderNonzeroBaseInput
        scanRemainderNonzeroBaseWrongOriginState 0 := by
  constructor
  · norm_num [sortSliceRangeKeys, sortSliceRangeEntries,
      canonicalOccurrenceSegment, tagOccurrences,
      scanRemainderNonzeroBaseInput,
      scanRemainderNonzeroBaseWrongOriginState,
      scanRemainderRegressionEntry]
  constructor
  · norm_num [sortSliceRangeKeys, sortSliceRangeEntries,
      scanRemainderNonzeroBaseInput,
      scanRemainderNonzeroBaseWrongOriginState,
      scanRemainderRegressionEntry]
  · intro h
    have hkeys := h.keys_eq
    norm_num [sortSliceRangeKeys, sortSliceRangeEntries,
      canonicalOccurrenceSegment, tagOccurrences,
      scanRemainderNonzeroBaseInput,
      scanRemainderNonzeroBaseWrongOriginState,
      scanRemainderRegressionEntry] at hkeys

end CPythonListsort

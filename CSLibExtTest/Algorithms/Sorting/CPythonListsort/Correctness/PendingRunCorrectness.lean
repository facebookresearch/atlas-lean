/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.PendingRunCorrectness

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Absolute-origin regressions -/

private def pendingRunsCorrectRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def pendingRunsCorrectRegressionEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

private def pendingRunsCorrectRegressionInput : Array Nat :=
  #[99, 7, 7, 777]

private def pendingRunsCorrectSuffixInput : Array Nat :=
  #[99, 7, 7, 888]

/-- A concrete state whose one pending run covers the nonzero-base consumed
segment `[1, 3)`.  Equal keys retain their absolute origins one and two, while
index three is deliberately left unscanned. -/
private def pendingRunsCorrectRegressionState :
    MergeState (Occurrence Nat) PUnit :=
  { min_gallop := 7
    listlen := 3
    basekeys := 1
    data :=
      { entries :=
          #[pendingRunsCorrectRegressionEntry 99 0,
            pendingRunsCorrectRegressionEntry 7 1,
            pendingRunsCorrectRegressionEntry 7 2,
            pendingRunsCorrectRegressionEntry 777 3] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[{ base := 1, len := 2, power := none }]
    key_compare := occurrenceComparator pendingRunsCorrectRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- The same state through the consumed endpoint, with only the unscanned
entry at absolute index three changed. -/
private def pendingRunsCorrectSuffixState :
    MergeState (Occurrence Nat) PUnit :=
  { pendingRunsCorrectRegressionState with
    data :=
      { entries :=
          #[pendingRunsCorrectRegressionEntry 99 0,
            pendingRunsCorrectRegressionEntry 7 1,
            pendingRunsCorrectRegressionEntry 7 2,
            pendingRunsCorrectRegressionEntry 888 3] } }

/-- Anti-vacuity witness for the complete invariant: a nonempty one-run stack
at nonzero `basekeys` satisfies layout, run sortedness, exact canonical
permutation, and stability of two comparator-equivalent occurrences. -/
private theorem pendingRunsCorrect_nonzeroBase_witness :
    PendingRunsCorrect pendingRunsCorrectRegressionLt
      pendingRunsCorrectRegressionInput pendingRunsCorrectRegressionState 2 := by
  norm_num [PendingRunsCorrect, PendingLayout, PendingRunsCover,
    PendingRun.endIndex, pendingRunOccurrenceKeys, pendingOccurrenceKeys,
    canonicalOccurrenceSegment, StableOccurrencePermutation, Sorted,
    ComparatorEquivalent, occurrenceComparator, tagOccurrences,
    pendingRunsCorrectRegressionLt, pendingRunsCorrectRegressionInput,
    pendingRunsCorrectRegressionState, pendingRunsCorrectRegressionEntry,
    PySSize.Nonnegative, BitVec.toNat_ofNat, BitVec.msb, BitVec.getMsbD,
    BitVec.getLsbD]
  all_goals decide

/-- Changing only the unscanned suffix changes both the input and backing
state observably, leaves the consumed canonical/pending sequences unchanged,
and preserves the complete invariant in both worlds. -/
private theorem pendingRunsCorrect_unscannedSuffix_freedom_regression :
    pendingRunsCorrectRegressionInput.extract 0 3 =
        pendingRunsCorrectSuffixInput.extract 0 3 ∧
      pendingRunsCorrectRegressionState.data.entries.extract 0 3 =
        pendingRunsCorrectSuffixState.data.entries.extract 0 3 ∧
      pendingRunsCorrectRegressionInput ≠ pendingRunsCorrectSuffixInput ∧
      pendingRunsCorrectRegressionState.data.entries ≠
        pendingRunsCorrectSuffixState.data.entries ∧
      canonicalOccurrenceSegment pendingRunsCorrectRegressionInput 1 2 =
        canonicalOccurrenceSegment pendingRunsCorrectSuffixInput 1 2 ∧
      pendingOccurrenceKeys pendingRunsCorrectRegressionState =
        pendingOccurrenceKeys pendingRunsCorrectSuffixState ∧
      PendingRunsCorrect pendingRunsCorrectRegressionLt
        pendingRunsCorrectRegressionInput pendingRunsCorrectRegressionState 2 ∧
      PendingRunsCorrect pendingRunsCorrectRegressionLt
        pendingRunsCorrectSuffixInput pendingRunsCorrectSuffixState 2 := by
  norm_num [PendingRunsCorrect, PendingLayout, PendingRunsCover,
    PendingRun.endIndex, pendingRunOccurrenceKeys, pendingOccurrenceKeys,
    canonicalOccurrenceSegment, StableOccurrencePermutation, Sorted,
    ComparatorEquivalent, occurrenceComparator, tagOccurrences,
    pendingRunsCorrectRegressionLt, pendingRunsCorrectRegressionInput,
    pendingRunsCorrectSuffixInput, pendingRunsCorrectRegressionState,
    pendingRunsCorrectSuffixState, pendingRunsCorrectRegressionEntry,
    PySSize.Nonnegative, BitVec.toNat_ofNat, BitVec.msb, BitVec.getMsbD,
    BitVec.getLsbD]
  all_goals decide

/-- A consumed segment beginning at one retains origins one and two. -/
private theorem canonicalOccurrenceSegment_absolute_origins_regression :
    canonicalOccurrenceSegment (#[10, 20, 30] : Array Nat) 1 2 =
      [{ value := 20, origin := 1 }, { value := 30, origin := 2 }] := by
  norm_num [canonicalOccurrenceSegment, tagOccurrences]

/-- Tagging the full input and then taking a nonzero-base segment is observably
different from the forbidden construction that extracts first and locally
retags the run from zero. -/
private theorem canonicalOccurrenceSegment_ne_local_retag_regression :
    canonicalOccurrenceSegment (#[10, 20, 30] : Array Nat) 1 2 ≠
      (tagOccurrences ((#[10, 20, 30] : Array Nat).extract 1 3)).toList := by
  norm_num [canonicalOccurrenceSegment, tagOccurrences]

end CPythonListsort

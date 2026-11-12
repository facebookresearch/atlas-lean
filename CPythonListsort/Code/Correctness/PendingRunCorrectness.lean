/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.Order
import Code.Policy.PendingLayout

/-!
# Pending-run correctness

This module joins the structural pending-stack invariant to the local
sortedness and occurrence-level stability facts needed by the later scan and
collapse proofs.  Origins are attached to the complete input before selecting
the consumed segment.  In particular, a run beginning away from index zero is
never retagged relative to its own beginning.
-/

namespace CPythonListsort

universe u v

/-- The occurrence-carrying keys currently stored in one pending run. -/
def pendingRunOccurrenceKeys (state : MergeState (Occurrence α) ν)
    (run : PendingRun) : Array (Occurrence α) :=
  (state.data.entries.extract run.base run.endIndex).map SortSliceEntry.key

/-- The occurrence-carrying keys of all pending runs, in stack/layout order. -/
def pendingOccurrenceKeys (state : MergeState (Occurrence α) ν) :
    List (Occurrence α) :=
  state.pending.toList.flatMap fun run =>
    (pendingRunOccurrenceKeys state run).toList

/-- Canonical tags for exactly `[base, base + scanned)` in the original input.

Tagging happens before extraction, so every retained origin is an absolute
index in `input`, rather than an index manufactured relative to this segment.
No element beyond the selected segment occurs in this definition. -/
def canonicalOccurrenceSegment (input : Array α) (base scanned : Nat) :
    List (Occurrence α) :=
  ((tagOccurrences input).extract base (base + scanned)).toList

/-- Correctness invariant for the already-consumed segment represented by the
pending stack.

It deliberately constrains neither the contents nor the order of the
unscanned suffix.  Comparator laws likewise remain outside the invariant and
are hypotheses only of the later preservation/correctness theorems. -/
def PendingRunsCorrect (lt : BoolComparator α) (input : Array α)
    (state : MergeState (Occurrence α) ν) (scanned : Nat) : Prop :=
  PendingLayout state scanned ∧
    (∀ run ∈ state.pending.toList,
      Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys state run)) ∧
    StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input state.basekeys scanned)
      (pendingOccurrenceKeys state)

namespace PendingRunsCorrect

/-- The structural layout component exported for policy and bounds proofs. -/
theorem layout
    {α : Type u} {ν : Type v} {lt : BoolComparator α}
    {input : Array α} {state : MergeState (Occurrence α) ν}
    {scanned : Nat}
    (h : PendingRunsCorrect lt input state scanned) :
    PendingLayout state scanned :=
  h.1

/-- Every run named by the pending stack is sorted under the value comparator. -/
theorem runSorted
    {α : Type u} {ν : Type v} {lt : BoolComparator α}
    {input : Array α} {state : MergeState (Occurrence α) ν}
    {scanned : Nat}
    (h : PendingRunsCorrect lt input state scanned)
    (run : PendingRun) (hrun : run ∈ state.pending.toList) :
    Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys state run) :=
  h.2.1 run hrun

/-- The stability component is exactly the shared predicate exported by the
stability-specification node, instantiated with the absolute-origin consumed
segment. -/
theorem stableOccurrencePermutation
    {α : Type u} {ν : Type v} {lt : BoolComparator α}
    {input : Array α} {state : MergeState (Occurrence α) ν}
    {scanned : Nat}
    (h : PendingRunsCorrect lt input state scanned) :
    StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input state.basekeys scanned)
      (pendingOccurrenceKeys state) :=
  h.2.2

/-- The concatenated pending keys are a permutation of exactly the canonical
absolute-origin tags for the consumed segment. -/
theorem pending_perm_canonical
    {α : Type u} {ν : Type v} {lt : BoolComparator α}
    {input : Array α} {state : MergeState (Occurrence α) ν}
    {scanned : Nat}
    (h : PendingRunsCorrect lt input state scanned) :
    (pendingOccurrenceKeys state).Perm
      (canonicalOccurrenceSegment input state.basekeys scanned) :=
  h.stableOccurrencePermutation.1

/-- Comparator-equivalent pending occurrences retain increasing absolute
origins in their current concatenated order. -/
theorem pending_stable
    {α : Type u} {ν : Type v} {lt : BoolComparator α}
    {input : Array α} {state : MergeState (Occurrence α) ν}
    {scanned : Nat}
    (h : PendingRunsCorrect lt input state scanned) :
    (pendingOccurrenceKeys state).Pairwise fun
      (earlier later : Occurrence α) =>
      ComparatorEquivalent lt earlier.value later.value →
        earlier.origin < later.origin :=
  h.stableOccurrencePermutation.2

end PendingRunsCorrect

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
theorem pendingRunsCorrect_nonzeroBase_witness :
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
theorem pendingRunsCorrect_unscannedSuffix_freedom_regression :
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
theorem canonicalOccurrenceSegment_absolute_origins_regression :
    canonicalOccurrenceSegment (#[10, 20, 30] : Array Nat) 1 2 =
      [{ value := 20, origin := 1 }, { value := 30, origin := 2 }] := by
  norm_num [canonicalOccurrenceSegment, tagOccurrences]

/-- Tagging the full input and then taking a nonzero-base segment is observably
different from the forbidden construction that extracts first and locally
retags the run from zero. -/
theorem canonicalOccurrenceSegment_ne_local_retag_regression :
    canonicalOccurrenceSegment (#[10, 20, 30] : Array Nat) 1 2 ≠
      (tagOccurrences ((#[10, 20, 30] : Array Nat).extract 1 3)).toList := by
  norm_num [canonicalOccurrenceSegment, tagOccurrences]

end CPythonListsort

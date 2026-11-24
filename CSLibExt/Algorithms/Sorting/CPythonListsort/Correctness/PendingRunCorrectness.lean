/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.Order
import CSLibExt.Algorithms.Sorting.CPythonListsort.Policy.PendingLayout

-- Preserve the imported development's original implicit type binders.
set_option autoImplicit true

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

end CPythonListsort

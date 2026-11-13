/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.Comparator
import Mathlib.Data.List.Sort

/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/

namespace CPythonListsort

universe u

/-- Mathlib's strict-weak-order laws for the Prop-valued relation exposed by a
Boolean comparator.  This structure deliberately contains no sorting result. -/
structure BoolStrictWeakOrder {α : Type u} (lt : BoolComparator α) : Prop extends
    IsStrictWeakOrder α (fun a b => lt a b = true)

/-- Comparator equivalence: neither value is strictly before the other. -/
def ComparatorEquivalent (lt : BoolComparator α) (a b : α) : Prop :=
  lt a b = false ∧ lt b a = false

theorem comparatorEquivalent_iff_incomparable (lt : BoolComparator α) (a b : α) :
    ComparatorEquivalent lt a b ↔
      ¬lt a b = true ∧ ¬lt b a = true := by
  simp [ComparatorEquivalent]

/-- Under the strict-weak-order laws, comparator equivalence really is an
equivalence relation.  This is the equivalence-class API used by stability
proofs; it adds no law to the definition of `ComparatorEquivalent` itself. -/
theorem BoolStrictWeakOrder.comparatorEquivalent_equivalence
    {lt : BoolComparator α} (h : BoolStrictWeakOrder lt) :
    Equivalence (ComparatorEquivalent lt) := by
  constructor
  · intro a
    rw [comparatorEquivalent_iff_incomparable]
    exact ⟨h.irrefl a, h.irrefl a⟩
  · intro a b hab
    rw [comparatorEquivalent_iff_incomparable] at hab ⊢
    exact ⟨hab.2, hab.1⟩
  · intro a b c hab hbc
    rw [comparatorEquivalent_iff_incomparable] at hab hbc ⊢
    exact h.incomp_trans a b c hab hbc

/-- An array is sorted when no later entry strictly precedes an earlier one. -/
def Sorted (lt : BoolComparator α) (ys : Array α) : Prop :=
  ys.toList.Pairwise (fun earlier later => lt later earlier = false)

/-- Index-facing form of `Sorted`, used by local loop invariants. -/
theorem sorted_iff_no_later_precedes (lt : BoolComparator α) (ys : Array α) :
    Sorted lt ys ↔
      ∀ i j (hi : i < ys.size) (hj : j < ys.size),
        i < j → ¬lt ys[j] ys[i] = true := by
  simpa [Sorted] using
    (List.pairwise_iff_getElem (l := ys.toList)
      (R := fun earlier later => lt later earlier = false))

/-- A value together with the position of that exact input occurrence. -/
structure Occurrence (α : Type u) where
  value : α
  origin : Nat
  deriving DecidableEq, Repr

/-- Attach immutable origin tags before sorting begins. -/
def tagOccurrences (xs : Array α) : Array (Occurrence α) :=
  xs.zipIdx.map fun entry =>
    { value := entry.1, origin := entry.2 }

/-- Compare tagged occurrences only through their externally visible values. -/
def occurrenceComparator (lt : BoolComparator α) : BoolComparator (Occurrence α) :=
  fun a b => lt a.value b.value

/-- Strict-weak-order laws lift through occurrence tagging because the
comparator deliberately ignores the immutable origin field.  Merge and scan
correctness use this public bridge when applying order theorems to the actual
tagged keys moved by the transcription. -/
theorem BoolStrictWeakOrder.occurrenceComparator
    {lt : BoolComparator α} (h : BoolStrictWeakOrder lt) :
    BoolStrictWeakOrder (occurrenceComparator lt) := by
  exact
    { toIsStrictWeakOrder :=
        { toIsStrictOrder :=
            { toIrrefl := ⟨fun occurrence => h.irrefl occurrence.value⟩
              toIsTrans :=
                ⟨fun first second third hfirstSecond hsecondThird =>
                  h.trans first.value second.value third.value hfirstSecond
                    hsecondThird⟩ }
          incomp_trans := fun first second third hfirstSecond hsecondThird =>
            h.incomp_trans first.value second.value third.value hfirstSecond
              hsecondThird } }

/-- Transitivity of the induced non-strict relation `¬ (b < a)`.  This is
the order-algebra bridge used by stable merge and run proofs. -/
theorem BoolStrictWeakOrder.false_trans
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {a b c : α}
    (hab : lt b a = false) (hbc : lt c b = false) :
    lt c a = false := by
  apply Bool.eq_false_iff.mpr
  intro hca
  have hab' : ¬lt b a = true := by simp [hab]
  have hbc' : ¬lt c b = true := by simp [hbc]
  by_cases hac : lt a b = true
  · exact hbc' (horder.trans c a b hca hac)
  have hincompAB : ¬lt a b = true ∧ ¬lt b a = true := ⟨hac, hab'⟩
  by_cases hbc : lt b c = true
  · exact hab' (horder.trans b c a hbc hca)
  have hincompBC : ¬lt b c = true ∧ ¬lt c b = true := ⟨hbc, hbc'⟩
  exact (horder.incomp_trans a b c hincompAB hincompBC).2 hca

/-- If `a < b` and `c` is not below `b`, then `a < c`. -/
theorem BoolStrictWeakOrder.strict_of_strict_of_not_reverse
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {a b c : α}
    (hab : lt a b = true) (hcb : lt c b = false) :
    lt a c = true := by
  by_cases hac : lt a c = true
  · exact hac
  by_cases hca : lt c a = true
  · have hcnb : ¬lt c b = true := by simp [hcb]
    exact False.elim (hcnb (horder.trans c a b hca hab))
  have hincompAC : ¬lt a c = true ∧ ¬lt c a = true := ⟨hac, hca⟩
  by_cases hbc : lt b c = true
  · exact horder.trans a b c hab hbc
  have hincompCB : ¬lt c b = true ∧ ¬lt b c = true :=
    ⟨by simp [hcb], hbc⟩
  exact False.elim ((horder.incomp_trans a c b hincompAC hincompCB).1 hab)

/-- If `b` is not below `a` and `b < c`, then `a < c`.  This is the
forward form needed to lift a strict final-element comparison across all
earlier elements of a sorted run. -/
theorem BoolStrictWeakOrder.strict_of_not_reverse_of_strict
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {a b c : α}
    (hba : lt b a = false) (hbc : lt b c = true) :
    lt a c = true := by
  by_cases hac : lt a c = true
  · exact hac
  have hacFalse : lt a c = false := Bool.eq_false_iff.mpr hac
  have hfalse : lt b c = false := horder.false_trans hacFalse hba
  exact False.elim (Bool.noConfusion (hfalse.symm.trans hbc))

/-- An occurrence sequence is a stable permutation of an explicitly chosen
canonical occurrence sequence.  This is the shared stability predicate for
both whole-sort results and intermediate consumed segments: callers choose the
canonical sequence, but may not retag the output after the fact. -/
def StableOccurrencePermutation (lt : BoolComparator α)
    (canonical output : List (Occurrence α)) : Prop :=
  output.Perm canonical ∧
    output.Pairwise fun earlier later =>
      ComparatorEquivalent lt earlier.value later.value →
        earlier.origin < later.origin

/-- A modeled output whose occurrence tags have travelled with its values. -/
structure TaggedOutput (α : Type u) where
  occurrences : Array (Occurrence α)
  deriving DecidableEq, Repr

/-- Erase carried origin tags to obtain the externally observable values. -/
def TaggedOutput.values (ys : TaggedOutput α) : Array α :=
  ys.occurrences.map Occurrence.value

/-- The tagged input from which a sorting execution starts.  Sorting code must
move these records, rather than manufacture origins after producing values. -/
def TaggedOutput.fromInput (xs : Array α) : TaggedOutput α :=
  ⟨tagOccurrences xs⟩

@[simp]
theorem TaggedOutput.values_fromInput (xs : Array α) :
    (TaggedOutput.fromInput xs).values = xs := by
  simp only [TaggedOutput.fromInput, TaggedOutput.values, tagOccurrences, Array.map_map]
  change xs.zipIdx.map Prod.fst = xs
  exact Array.zipIdx_map_fst 0 xs

/-- Occurrence-level stability.  The permutation clause ties every final tag
to the canonical tag attached to the input, while the pairwise clause keeps
comparator-equivalent occurrences in increasing original-index order. -/
def Stable (lt : BoolComparator α) (xs : Array α) (ys : TaggedOutput α) : Prop :=
  StableOccurrencePermutation lt (tagOccurrences xs).toList
    ys.occurrences.toList

/-- The public whole-sort stability predicate is definitionally the shared
stable-occurrence predicate instantiated with the canonically tagged input. -/
theorem stable_iff_stableOccurrencePermutation (lt : BoolComparator α)
    (xs : Array α) (ys : TaggedOutput α) :
    Stable lt xs ys ↔
      StableOccurrencePermutation lt (tagOccurrences xs).toList
        ys.occurrences.toList :=
  Iff.rfl

end CPythonListsort

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 340, Logic 355, Logic 356, Logic 357
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal Set Order

-- Logic 340: Subset mod finite
def SubsetModFinite {α : Type*} (a b : Set α) : Prop := (a \ b).Finite

theorem subsetModFinite_refl {α : Type*} (a : Set α) : SubsetModFinite a a := by
  simp [SubsetModFinite]

theorem subsetModFinite_trans {α : Type*} {a b c : Set α}
    (hab : SubsetModFinite a b) (hbc : SubsetModFinite b c) : SubsetModFinite a c := by
  refine Set.Finite.subset (hab.union hbc) ?_
  intro x hx
  by_cases hb : x ∈ b
  · exact Or.inr ⟨hb, hx.2⟩
  · exact Or.inl ⟨hx.1, hb⟩

theorem subsetModFinite_of_subset {α : Type*} {a b : Set α} (h : a ⊆ b) :
    SubsetModFinite a b := by
  have : a \ b = ∅ := Set.sdiff_eq_empty.mpr h
  rw [SubsetModFinite, this]
  exact Set.finite_empty

theorem not_antisymm_subsetModFinite :
    ∃ a b : Set ℕ, SubsetModFinite a b ∧ SubsetModFinite b a ∧ a ≠ b := by
  refine ⟨{0}, ∅, ?_, ?_, ?_⟩
  · rw [SubsetModFinite, Set.sdiff_empty]
    exact Set.finite_singleton 0
  · exact subsetModFinite_of_subset (Set.empty_subset _)
  · intro h
    have : (0 : ℕ) ∈ ({0} : Set ℕ) := rfl
    rw [h] at this
    exact this

-- Logic 355: P-ideal
structure IsPIdeal {α : Type*} (I : Set (Set α)) : Prop where
  countable : ∀ a ∈ I, a.Countable
  downward : ∀ a ∈ I, ∀ b ⊆ a, b ∈ I
  finite_mem : ∀ a : Set α, a.Finite → a ∈ I
  union_mem : ∀ a ∈ I, ∀ b ∈ I, a ∪ b ∈ I
  sigma_directed : ∀ f : ℕ → Set α, (∀ n, f n ∈ I) → ∃ b ∈ I, ∀ n, SubsetModFinite (f n) b

theorem isPIdeal_singleton_empty_fails {α : Type*} (x : α) :
    ¬ IsPIdeal ({∅} : Set (Set α)) := by
  intro h
  have hx := h.finite_mem {x} (Set.finite_singleton x)
  rw [Set.mem_singleton_iff] at hx
  have : x ∈ ({x} : Set α) := rfl
  rw [hx] at this
  exact this

-- Logic 356: Is Orthogonal To
def IsOrthogonalTo {α : Type*} (I : Set (Set α)) (X : Set α) : Prop :=
  ∀ a ∈ I, (X ∩ a).Finite

theorem isOrthogonalTo_empty {α : Type*} (I : Set (Set α)) :
    IsOrthogonalTo I (∅ : Set α) := by
  intro a _
  rw [Set.empty_inter]
  exact Set.finite_empty

-- Logic 357: P-ideal dichotomy
def PIdealDichotomy.{u} : Prop :=
  ∀ (α : Type u) (I : Set (Set α)), ¬ (Set.univ : Set α).Countable → IsPIdeal I →
    (∃ A : Set α, ¬ A.Countable ∧ ∀ x ∈ CountableSubsets α, x ⊆ A → x ∈ I) ∨
    (∃ F : ℕ → Set α, (⋃ n, F n) = Set.univ ∧ ∀ n, IsOrthogonalTo I (F n))

theorem finite_inter_of_good_of_orthogonal {α : Type*} {I : Set (Set α)} {A X : Set α}
    (hA : ∀ x ∈ CountableSubsets α, x ⊆ A → x ∈ I) (hX : IsOrthogonalTo I X) :
    (A ∩ X).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨e, he⟩ := Set.Infinite.natEmbedding _ hinf
  set x : Set α := Set.range (fun n : ℕ => ((e n : ↥(A ∩ X)) : α)) with hxdef
  have hxsub : x ⊆ A ∩ X := by
    rintro y ⟨n, rfl⟩
    exact (e n).2
  have hxc : x.Countable := Set.countable_range _
  have hxI : x ∈ I := hA x hxc (fun y hy => (hxsub hy).1)
  have hfin : (X ∩ x).Finite := hX x hxI
  have hXx : X ∩ x = x := Set.inter_eq_right.mpr (fun y hy => (hxsub hy).2)
  rw [hXx] at hfin
  have hinj : Function.Injective (fun n : ℕ => ((e n : ↥(A ∩ X)) : α)) := by
    intro a b hab
    exact he (Subtype.ext hab)
  exact (Set.infinite_range_of_injective hinj) hfin

theorem not_both_alternatives {α : Type*} {I : Set (Set α)} {A : Set α}
    (hAunc : ¬ A.Countable) (hA : ∀ x ∈ CountableSubsets α, x ⊆ A → x ∈ I)
    (F : ℕ → Set α) (hcov : (⋃ n, F n) = Set.univ)
    (horth : ∀ n, IsOrthogonalTo I (F n)) : False := by
  refine hAunc ?_
  have hsplit : A = ⋃ n, (A ∩ F n) := by
    rw [← Set.inter_iUnion, hcov, Set.inter_univ]
  rw [hsplit]
  exact Set.countable_iUnion fun n =>
    (finite_inter_of_good_of_orthogonal hA (horth n)).countable

end

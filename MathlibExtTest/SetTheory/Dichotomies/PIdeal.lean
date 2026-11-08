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

public import MathlibExt.SetTheory.Dichotomies.PIdeal
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

open Cardinal Ordinal Set Order

namespace MathlibExtTest.SetTheory.Dichotomies.PIdeal

open MetaMathlibExt

-- Logic 340: Subset mod finite

theorem subsetModFinite_refl {α : Type*} (a : Set α) : SubsetModFinite a a := by
  simp [SubsetModFinite]

theorem subsetModFinite_trans {α : Type*} {a b c : Set α}
    (hab : SubsetModFinite a b) (hbc : SubsetModFinite b c) : SubsetModFinite a c := by
  refine Set.Finite.subset (hab.union hbc) ?_
  intro x hx
  by_cases hb : x ∈ b
  · exact Or.inr ⟨hb, hx.2⟩
  · exact Or.inl ⟨hx.1, hb⟩

/-- Genuine inclusion is the degenerate case. -/

theorem subsetModFinite_of_subset {α : Type*} {a b : Set α} (h : a ⊆ b) :
    SubsetModFinite a b := by
  have : a \ b = ∅ := Set.sdiff_eq_empty.mpr h
  rw [SubsetModFinite, this]
  exact Set.finite_empty

/-- **Not antisymmetric**, so this is a preorder only — which is why `IsPIdeal.sigma_directed`
asks for an upper bound and not a least one. -/

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

/-- **`finite_mem` is not redundant**: `{∅}` satisfies every other field but omits `{x}`. -/

theorem isPIdeal_singleton_empty_fails {α : Type*} (x : α) :
    ¬ IsPIdeal ({∅} : Set (Set α)) := by
  intro h
  have hx := h.finite_mem {x} (Set.finite_singleton x)
  rw [Set.mem_singleton_iff] at hx
  have : x ∈ ({x} : Set α) := rfl
  rw [hx] at this
  exact this

-- Logic 356: Is Orthogonal To

/-- `∅` is orthogonal to every family. -/

theorem isOrthogonalTo_empty {α : Type*} (I : Set (Set α)) :
    IsOrthogonalTo I (∅ : Set α) := by
  intro a _
  rw [Set.empty_inter]
  exact Set.finite_empty

-- Logic 357: P-ideal dichotomy

/-- **The alternatives are exclusive, step 1.**  A set all of whose countable subsets lie in `I`
meets every `I`-orthogonal set finitely. -/

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

/-- **The alternatives are exclusive**, so `PIdealDichotomy` is a real dichotomy. -/

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

end MathlibExtTest.SetTheory.Dichotomies.PIdeal

end

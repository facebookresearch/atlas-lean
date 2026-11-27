/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DirectProductFactorCardinalityKourovka21Problem58
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Minimal
import Mathlib.Tactic.ByContra

/-! # Tests for `MathlibExt.GroupTheory.DirectProductFactorCardinalityKourovka21Problem58` -/

namespace MathlibExtTest.DirectProductFactorCardinalityKourovka21Problem58

open MathlibExt.GroupTheory.DirectProductFactorCardinalityKourovka21Problem58Wanted

-- Test section: direct products of subsets.
-- An empty first factor makes every product direct.
example {G : Type} [Group G] (B : Set G) : IsDirectProduct ∅ B :=
  fun _ ha₁ => absurd ha₁ (Set.notMem_empty _)

-- A one-element first factor also makes every product direct, so the whole group is its only
-- maximal direct factor.
example {G : Type} [Group G] (g : G) (B : Set G) :
    Maximal (IsDirectProduct {g}) B ↔ B = Set.univ := by
  have hdir (C : Set G) : IsDirectProduct {g} C := by
    rintro a₁ rfl a₂ rfl b₁ - b₂ - h
    exact ⟨rfl, mul_left_cancel h⟩
  exact ⟨fun h => h.eq_of_le (hdir _) (Set.subset_univ _),
    fun h => h ▸ ⟨hdir _, fun _ _ _ => Set.subset_univ _⟩⟩

-- In `ℤ`, written multiplicatively, the sum `{0, 1} + {0, 2}` is direct.
example : IsDirectProduct ({1, Multiplicative.ofAdd 1} : Set (Multiplicative ℤ))
    {1, Multiplicative.ofAdd 2} := by
  simp only [IsDirectProduct, Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro a₁ (rfl | rfl) a₂ (rfl | rfl) b₁ (rfl | rfl) b₂ (rfl | rfl) h <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

-- The product `{1, g} {1, g}` is not direct when `g ≠ 1`: `g = g * 1 = 1 * g`.
example {G : Type} [Group G] (g : G) (hg : g ≠ 1) : ¬ IsDirectProduct {1, g} {1, g} := by
  intro h
  have := h g (by simp) 1 (by simp) 1 (by simp) g (by simp) (by simp)
  exact hg this.1

-- Test section: the refutation of Kourovka 21.58.
-- Infiniteness is needed: in the trivial group, every maximal direct factor is the whole group.
example (A B₁ B₂ : Set Unit) (h₁ : Maximal (IsDirectProduct A) B₁)
    (h₂ : Maximal (IsDirectProduct A) B₂) : Cardinal.mk B₁ = Cardinal.mk B₂ := by
  have huniv : IsDirectProduct A Set.univ := fun _ _ _ _ _ _ _ _ _ =>
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  rw [h₁.eq_of_le huniv (Set.subset_univ _), h₂.eq_of_le huniv (Set.subset_univ _)]

-- Every infinite group has maximal direct factors of different cardinalities.
example (G : Type) [Group G] [Infinite G] : ∃ A B₁ B₂ : Set G, Maximal (IsDirectProduct A) B₁ ∧
    Maximal (IsDirectProduct A) B₂ ∧ Cardinal.mk B₁ ≠ Cardinal.mk B₂ := by
  by_contra! h
  exact existsInfiniteGroupStableFactors_refuted ⟨G, inferInstance, inferInstance, h⟩

-- In particular, the infinite cyclic group is not such a group.
example : ¬ ∀ A B₁ B₂ : Set (Multiplicative ℤ), Maximal (IsDirectProduct A) B₁ →
    Maximal (IsDirectProduct A) B₂ → Cardinal.mk B₁ = Cardinal.mk B₂ :=
  fun h => existsInfiniteGroupStableFactors_refuted ⟨Multiplicative ℤ, inferInstance,
    inferInstance, h⟩

end MathlibExtTest.DirectProductFactorCardinalityKourovka21Problem58

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.Cardinal.Cofinality.Stationary
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

open Cardinal Ordinal

namespace MathlibExtTest.SetTheory.Cardinal.Cofinality.Stationary

open MetaMathlibExt

-- Logic 42: Contains all bounded sets

/-- Sanity check (satisfiability, meaningfully): the family of bounded sets itself
contains all bounded sets.  So `ContainsAllBounded` is witnessed by the very ideal the
singular-`κ` theorem is about, not just by `univ`. -/

theorem containsAllBounded_setOf_bounded.{u} (κ : Cardinal.{u}) :
    ContainsAllBounded κ
      {X : Set (Set.Iio κ.ord) | ∃ β : Set.Iio κ.ord, ∀ α ∈ X, (α : Ordinal) < (β : Ordinal)} :=
  fun _ hX => hX

-- Logic 52: $\kappa$-complete ideal

/-- Sanity check: `IsKappaCompleteIdeal` is satisfiable.  For any proper subset `A`
of `κ`, the principal ideal `{X | X ⊆ A}` is a `κ`-complete ideal.  In particular
`empty_mem` and `univ_not_mem` are jointly consistent, so the four fields do not
contradict each other and the structure is not vacuously uninhabited. -/

theorem isKappaCompleteIdeal_principal.{u} (κ : Cardinal.{u})
    (A : Set (Set.Iio κ.ord)) (hA : A ≠ Set.univ) :
    IsKappaCompleteIdeal κ {X | X ⊆ A} where
  downward := fun _ hX _ hY => hY.trans hX
  empty_mem := Set.empty_subset A
  univ_not_mem := fun h => hA (Set.univ_subset_iff.mp h)
  kappa_complete := fun _ _ hF => Set.sUnion_subset hF

/-- Corollary: a concrete witness, taking `A = ∅`.  Requires `κ ≠ 0` so that `κ` has
at least one element and `∅ ≠ Set.univ`. -/

theorem isKappaCompleteIdeal_bot.{u} (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    IsKappaCompleteIdeal κ {X : Set (Set.Iio κ.ord) | X ⊆ ∅} := by
  refine isKappaCompleteIdeal_principal κ ∅ ?_
  intro h
  have : Nonempty (Set.Iio κ.ord) := by
    refine ⟨⟨0, ?_⟩⟩
    exact Cardinal.ord_pos.2 (aleph0_pos.trans_le hκ)
  obtain ⟨x⟩ := this
  exact absurd (h ▸ Set.mem_univ x) (Set.notMem_empty x)

-- Logic 53: Normal ideal on $\kappa$

/-- Sanity check 1 (satisfiability): every principal family `{X | X ⊆ A₀}` is normal,
since a diagonal union is contained in the union of the `A ξ`.  So `IsNormalIdeal` is
not vacuously uninhabited. -/

theorem isNormalIdeal_principal.{u} (κ : Cardinal.{u}) (A₀ : Set (Set.Iio κ.ord)) :
    IsNormalIdeal κ {X | X ⊆ A₀} := by
  intro A hA α hα
  obtain ⟨ξ, _, hmem⟩ := hα
  exact hA ξ hmem

/-- Sanity check 2 (the `ξ < α` clause is load-bearing): the diagonal union of the
constant sequence `A ξ = univ` is exactly the nonzero part of `κ`, not all of `κ`.
Under a definition that dropped `ξ < α` this would be `univ`, so this equality is
precisely what fails if the strict inequality is removed.  It also exercises the
`(ξ : Ordinal)` coercion. -/

theorem diagonalUnion_const_univ.{u} (κ : Cardinal.{u}) :
    {α : Set.Iio κ.ord | ∃ ξ : Set.Iio κ.ord,
      (ξ : Ordinal) < α ∧ α ∈ (Set.univ : Set (Set.Iio κ.ord))}
      = {α : Set.Iio κ.ord | (0 : Ordinal) < (α : Ordinal)} := by
  ext α
  constructor
  · rintro ⟨ξ, hξ, -⟩
    exact lt_of_le_of_lt zero_le hξ
  · intro hα
    have h0' : (0 : Ordinal) ∈ Set.Iio κ.ord := Set.mem_Iio.2 (lt_of_le_of_lt zero_le α.2)
    exact ⟨⟨0, h0'⟩, hα, Set.mem_univ _⟩

/-- Corollary of check 2: `0` is not in that diagonal union. -/

theorem zero_notMem_diagonalUnion_const_univ.{u} (κ : Cardinal.{u})
    (h0 : (0 : Ordinal) < κ.ord) :
    (⟨0, h0⟩ : Set.Iio κ.ord) ∉
      {α : Set.Iio κ.ord | ∃ ξ : Set.Iio κ.ord,
        (ξ : Ordinal) < α ∧ α ∈ (Set.univ : Set (Set.Iio κ.ord))} := by
  rw [diagonalUnion_const_univ]
  simp

-- Logic 2: Regressive function

/-- Sanity check: the constant-0 function is regressive.
    (Requires `0 < κ.ord` so that `0` is a valid point below κ.) -/

theorem const_zero_isRegressive.{u}
    (κ : Cardinal.{u}) (hκ : 0 < κ.ord) (S : Set (Set.Iio κ.ord)) :
    IsRegressive κ S (fun _ => ⟨0, hκ⟩) := by
  intro x hx
  show (0 : Ordinal) < (x : Ordinal)
  exact pos_of_ne_zero hx

end MathlibExtTest.SetTheory.Cardinal.Cofinality.Stationary

end

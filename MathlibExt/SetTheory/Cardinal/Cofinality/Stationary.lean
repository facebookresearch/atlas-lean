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

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Ordinal.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 1, Logic 42, Logic 52, Logic 53, Logic 2
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal

-- Logic 1 (IsStationary) REMOVED: Mathlib v4.34 now provides an identical definition at
-- Mathlib/SetTheory/Cardinal/Cofinality/Club.lean:228 (`@[expose] def IsStationary`).
-- Same statement, same hypotheses. Ours is redundant; this file relies on Mathlib's.

-- Logic 42: Contains all bounded sets
def ContainsAllBounded.{u} (κ : Cardinal.{u}) (I : Set (Set (Set.Iio κ.ord))) : Prop :=
  ∀ X : Set (Set.Iio κ.ord),
    (∃ β : Set.Iio κ.ord, ∀ α ∈ X, (α : Ordinal) < (β : Ordinal)) → X ∈ I

theorem containsAllBounded_setOf_bounded.{u} (κ : Cardinal.{u}) :
    ContainsAllBounded κ
      {X : Set (Set.Iio κ.ord) | ∃ β : Set.Iio κ.ord, ∀ α ∈ X, (α : Ordinal) < (β : Ordinal)} :=
  fun _ hX => hX

-- Logic 52: $\kappa$-complete ideal
structure IsKappaCompleteIdeal.{u} (κ : Cardinal.{u})
    (I : Set (Set (Set.Iio κ.ord))) : Prop where
  downward : ∀ X ∈ I, ∀ Y ⊆ X, Y ∈ I
  empty_mem : (∅ : Set (Set.Iio κ.ord)) ∈ I
  univ_not_mem : (Set.univ : Set (Set.Iio κ.ord)) ∉ I
  kappa_complete : ∀ F : Set (Set (Set.Iio κ.ord)),
    #F < Cardinal.lift.{u+1} κ → (∀ X ∈ F, X ∈ I) → ⋃₀ F ∈ I

theorem isKappaCompleteIdeal_principal.{u} (κ : Cardinal.{u})
    (A : Set (Set.Iio κ.ord)) (hA : A ≠ Set.univ) :
    IsKappaCompleteIdeal κ {X | X ⊆ A} where
  downward := fun _ hX _ hY => hY.trans hX
  empty_mem := Set.empty_subset A
  univ_not_mem := fun h => hA (Set.univ_subset_iff.mp h)
  kappa_complete := fun _ _ hF => Set.sUnion_subset hF

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
def IsNormalIdeal.{u} (κ : Cardinal.{u}) (I : Set (Set (Set.Iio κ.ord))) : Prop :=
  ∀ (A : Set.Iio κ.ord → Set (Set.Iio κ.ord)),
    (∀ ξ, A ξ ∈ I) →
    {α : Set.Iio κ.ord | ∃ ξ : Set.Iio κ.ord, (ξ : Ordinal) < α ∧ α ∈ A ξ} ∈ I

theorem isNormalIdeal_principal.{u} (κ : Cardinal.{u}) (A₀ : Set (Set.Iio κ.ord)) :
    IsNormalIdeal κ {X | X ⊆ A₀} := by
  intro A hA α hα
  obtain ⟨ξ, _, hmem⟩ := hα
  exact hA ξ hmem

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

theorem zero_notMem_diagonalUnion_const_univ.{u} (κ : Cardinal.{u})
    (h0 : (0 : Ordinal) < κ.ord) :
    (⟨0, h0⟩ : Set.Iio κ.ord) ∉
      {α : Set.Iio κ.ord | ∃ ξ : Set.Iio κ.ord,
        (ξ : Ordinal) < α ∧ α ∈ (Set.univ : Set (Set.Iio κ.ord))} := by
  rw [diagonalUnion_const_univ]
  simp

-- Logic 2: Regressive function
def IsRegressive (κ : Cardinal)
    (S : Set (Set.Iio κ.ord)) (f : ↥S → Set.Iio κ.ord) : Prop :=
  ∀ x : ↥S, (x : Ordinal) ≠ 0 → (f x : Ordinal) < (x : Ordinal)

theorem const_zero_isRegressive.{u}
    (κ : Cardinal.{u}) (hκ : 0 < κ.ord) (S : Set (Set.Iio κ.ord)) :
    IsRegressive κ S (fun _ => ⟨0, hκ⟩) := by
  intro x hx
  show (0 : Ordinal) < (x : Ordinal)
  exact pos_of_ne_zero hx

end

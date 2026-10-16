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

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 351, Logic 352
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 351: Equal mod finite
def EqModFinite (A B : Set ℕ) : Prop := (symmDiff A B).Finite


theorem eqModFinite_refl (A : Set ℕ) : EqModFinite A A := by
  simp [EqModFinite]


theorem eqModFinite_symm {A B : Set ℕ} (h : EqModFinite A B) : EqModFinite B A := by
  rwa [EqModFinite, symmDiff_comm]


theorem eqModFinite_trans {A B C : Set ℕ} (hab : EqModFinite A B) (hbc : EqModFinite B C) :
    EqModFinite A C :=
  Set.Finite.subset (hab.union hbc) (symmDiff_triangle A B C)

-- Logic 352: $P(\omega)\slash \textrm{fin}$ automorphism

structure IsPowModFiniteAutomorphism (Φ : Set ℕ → Set ℕ) : Prop where
  respects : ∀ A B : Set ℕ, EqModFinite A B → EqModFinite (Φ A) (Φ B)
  inter : ∀ A B : Set ℕ, EqModFinite (Φ (A ∩ B)) (Φ A ∩ Φ B)
  compl : ∀ A : Set ℕ, EqModFinite (Φ Aᶜ) (Φ A)ᶜ
  injective : ∀ A B : Set ℕ, EqModFinite (Φ A) (Φ B) → EqModFinite A B
  surjective : ∀ B : Set ℕ, ∃ A : Set ℕ, EqModFinite (Φ A) B

end

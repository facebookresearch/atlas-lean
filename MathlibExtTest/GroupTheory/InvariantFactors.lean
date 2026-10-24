/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.InvariantFactors

@[expose] public section

open scoped DirectSum

/-- The cardinality of a direct sum of cyclic groups is the product of the
orders. -/
private theorem natCard_directSum_zmod (k : ℕ) (d : Fin k → ℕ) :
    Nat.card (⨁ i : Fin k, ZMod (d i)) = ∏ i, d i := by
  rw [Nat.card_congr (DirectSum.addEquivProd _).toEquiv, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.card_zmod]

/-- For `ZMod 6` the decomposition has total size `6`. -/
example : ∃ (k : ℕ) (d : Fin k → ℕ),
    (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
    (∏ i, d i) = 6 ∧ Nonempty (ZMod 6 ≃+ ⨁ i : Fin k, ZMod (d i)) := by
  obtain ⟨k, d, hd1, hdvd, ⟨e⟩⟩ := exists_invariant_factor_decomposition_finite (ZMod 6)
  refine ⟨k, d, hd1, hdvd, ?_, ⟨e⟩⟩
  have hcard : Nat.card (ZMod 6) = Nat.card (⨁ i : Fin k, ZMod (d i)) :=
    Nat.card_congr e.toEquiv
  rw [Nat.card_zmod, natCard_directSum_zmod] at hcard
  exact hcard.symm

/-- For `ZMod 4 × ZMod 6` the decomposition has total size `24`. (The chain
condition rules out the elementary divisors `(4, 6)` as invariant
factors.) -/
example : ∃ (k : ℕ) (d : Fin k → ℕ),
    (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
    (∏ i, d i) = 24 ∧
    Nonempty ((ZMod 4 × ZMod 6) ≃+ ⨁ i : Fin k, ZMod (d i)) := by
  obtain ⟨k, d, hd1, hdvd, ⟨e⟩⟩ :=
    exists_invariant_factor_decomposition_finite (ZMod 4 × ZMod 6)
  refine ⟨k, d, hd1, hdvd, ?_, ⟨e⟩⟩
  have hcard : Nat.card (ZMod 4 × ZMod 6) = Nat.card (⨁ i : Fin k, ZMod (d i)) :=
    Nat.card_congr e.toEquiv
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, natCard_directSum_zmod] at hcard
  exact hcard.symm

/-- For `ℤ` the decomposition has a positive free rank. -/
example : ∃ (a k : ℕ) (d : Fin k → ℕ),
    (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
    1 ≤ a ∧ Nonempty (ℤ ≃+ (Fin a →₀ ℤ) × ⨁ i : Fin k, ZMod (d i)) := by
  obtain ⟨a, k, d, hd1, hdvd, ⟨e⟩⟩ := exists_invariant_factor_decomposition ℤ
  refine ⟨a, k, d, hd1, hdvd, ?_, ⟨e⟩⟩
  by_contra ha
  have ha0 : a = 0 := by omega
  subst ha0
  have hcard : Nat.card ℤ = Nat.card ((Fin 0 →₀ ℤ) × ⨁ i : Fin k, ZMod (d i)) :=
    Nat.card_congr e.toEquiv
  rw [Nat.card_prod, natCard_directSum_zmod] at hcard
  have hfree : Nat.card (Fin 0 →₀ ℤ) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, inferInstance⟩
  have hprod : 0 < ∏ i, d i :=
    Finset.prod_pos fun i _ => by have := hd1 i; omega
  have hZ : Nat.card ℤ = 0 := Nat.card_eq_zero.mpr (Or.inr inferInstance)
  rw [hfree, one_mul, hZ] at hcard
  omega

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.InvariantFactors
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

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
  obtain ⟨k, d, hd1, hdvd, ⟨e⟩⟩ :=
    AddCommGroup.equiv_directSum_invariant_factors_of_finite (ZMod 6)
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
    AddCommGroup.equiv_directSum_invariant_factors_of_finite (ZMod 4 × ZMod 6)
  refine ⟨k, d, hd1, hdvd, ?_, ⟨e⟩⟩
  have hcard : Nat.card (ZMod 4 × ZMod 6) = Nat.card (⨁ i : Fin k, ZMod (d i)) :=
    Nat.card_congr e.toEquiv
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, natCard_directSum_zmod] at hcard
  exact hcard.symm

/-- For `ℤ` the decomposition has a positive free rank. -/
example : ∃ (a k : ℕ) (d : Fin k → ℕ),
    (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
    1 ≤ a ∧ Nonempty (ℤ ≃+ (Fin a →₀ ℤ) × ⨁ i : Fin k, ZMod (d i)) := by
  obtain ⟨a, k, d, hd1, hdvd, ⟨e⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_invariant_factors ℤ
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

/-- A group with both a free part and torsion retains a positive free rank. -/
example : ∃ (a k : ℕ) (d : Fin k → ℕ),
    (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
    1 ≤ a ∧ Nonempty ((ℤ × ZMod 6) ≃+ (Fin a →₀ ℤ) × ⨁ i : Fin k, ZMod (d i)) := by
  obtain ⟨a, k, d, hd1, hdvd, ⟨e⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_invariant_factors (ℤ × ZMod 6)
  refine ⟨a, k, d, hd1, hdvd, ?_, ⟨e⟩⟩
  by_contra ha
  have ha0 : a = 0 := by omega
  subst ha0
  have hcard : Nat.card (ℤ × ZMod 6) =
      Nat.card ((Fin 0 →₀ ℤ) × ⨁ i : Fin k, ZMod (d i)) := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, Nat.card_prod, natCard_directSum_zmod] at hcard
  have hfree : Nat.card (Fin 0 →₀ ℤ) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, inferInstance⟩
  have hprod : 0 < ∏ i, d i :=
    Finset.prod_pos fun i _ => by have := hd1 i; omega
  have hZ : Nat.card ℤ = 0 := Nat.card_eq_zero.mpr (Or.inr inferInstance)
  rw [hfree, one_mul, hZ, zero_mul] at hcard
  omega

/-- The prime-power summands of orders `4` and `9` reorganize with total order `36`. -/
example : ∃ (k : ℕ) (d : Fin k → ℕ),
    (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
    (∏ i, d i) = 36 ∧
    Nonempty ((⨁ i : Fin 2, ZMod ((if i = 0 then 2 else 3) ^ 2)) ≃+
      ⨁ i : Fin k, ZMod (d i)) := by
  have hp : ∀ i : Fin 2, Nat.Prime (if i = 0 then 2 else 3) := by
    intro i
    split_ifs <;> decide
  obtain ⟨k, d, hd1, hdvd, ⟨e⟩⟩ :=
    AddCommGroup.elementary_divisors_equiv_invariant_factors (Fin 2)
      (fun i => if i = 0 then 2 else 3) hp (fun _ => 2)
  refine ⟨k, d, hd1, hdvd, ?_, ⟨e⟩⟩
  have hcard := Nat.card_congr e.toEquiv
  rw [natCard_directSum_zmod, natCard_directSum_zmod] at hcard
  norm_num [Fin.prod_univ_succ] at hcard
  exact hcard.symm

/-- Exponent zero is allowed by the source and gives total order `1`. -/
example : ∃ (k : ℕ) (d : Fin k → ℕ),
    (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
    (∏ i, d i) = 1 ∧
    Nonempty ((⨁ _ : Fin 1, ZMod (2 ^ 0)) ≃+ ⨁ i : Fin k, ZMod (d i)) := by
  obtain ⟨k, d, hd1, hdvd, ⟨e⟩⟩ :=
    AddCommGroup.elementary_divisors_equiv_invariant_factors (Fin 1)
      (fun _ => 2) (by intro i; decide) (fun _ => 0)
  refine ⟨k, d, hd1, hdvd, ?_, ⟨e⟩⟩
  have hcard := Nat.card_congr e.toEquiv
  rw [natCard_directSum_zmod, natCard_directSum_zmod] at hcard
  norm_num [Fin.prod_univ_succ] at hcard
  exact hcard.symm

/-- An empty family of prime-power summands gives total order `1`. -/
example : ∃ (k : ℕ) (d : Fin k → ℕ),
    (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
    (∏ i, d i) = 1 ∧
    Nonempty ((⨁ _ : Fin 0, ZMod (2 ^ 1)) ≃+ ⨁ i : Fin k, ZMod (d i)) := by
  obtain ⟨k, d, hd1, hdvd, ⟨e⟩⟩ :=
    AddCommGroup.elementary_divisors_equiv_invariant_factors (Fin 0)
      (fun _ => 2) (by intro i; decide) (fun _ => 1)
  refine ⟨k, d, hd1, hdvd, ?_, ⟨e⟩⟩
  have hcard := Nat.card_congr e.toEquiv
  rw [natCard_directSum_zmod, natCard_directSum_zmod] at hcard
  norm_num at hcard
  exact hcard.symm

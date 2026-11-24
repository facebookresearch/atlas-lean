/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.ZMod
import MathlibExt.NumberTheory.FunctionField.KappaPowMoebius

/-! # Tests for variable powers and the Möbius bound over the field with two elements -/

open Polynomial UniqueFactorizationMonoid

namespace MetaMathlibExt.abs_sum_moebius_kappaPow_le

private noncomputable def exponents (p : (ZMod 2)[X]) : ℕ :=
  open Classical in if p = X then 3 else 2

private theorem other_prime_ne_X : X - C (1 : ZMod 2) ≠ X := by
  intro h
  have hcoeff := congrArg (fun p : (ZMod 2)[X] ↦ p.coeff 0) h
  simp at hcoeff

private theorem two_le_exponents (p : (ZMod 2)[X]) : 2 ≤ exponents p := by
  unfold exponents
  split <;> decide

private theorem minimum_eq_two : kappaMin exponents = 2 := by
  apply le_antisymm
  · simpa [exponents, other_prime_ne_X] using
      kappaMin_le exponents (monic_X_sub_C 1) (irreducible_X_sub_C 1)
  · let : Nonempty {P : (ZMod 2)[X] // P.Monic ∧ Irreducible P} :=
      ⟨⟨X, monic_X, irreducible_X⟩⟩
    exact le_ciInf fun p ↦ two_le_exponents p

-- The minimum is attained at the linear prime whose weight is smaller than the weight of X.
example : kappaMin exponents < exponents X := by
  norm_num [minimum_eq_two, exponents]

-- The two copies of X each contribute their full exponent.
example : kappaPow exponents (X ^ 2 * (X - C 1)) = X ^ 6 * (X - C 1) ^ 2 := by
  suffices h : ∀ (F : Type) [Field F] (κ : F[X] → ℕ),
      kappaPow κ (X ^ 2 * (X - C 1)) = (X ^ κ X) ^ 2 * (X - C 1) ^ κ (X - C 1) by
    rw [h]
    simp [exponents, ← pow_mul]
  intro F _ κ
  classical
  rw [kappaPow, normalizedFactors_mul (pow_ne_zero _ X_ne_zero) (monic_X_sub_C 1).ne_zero,
    irreducible_X.normalizedFactors_pow, normalizedFactors_irreducible (irreducible_X_sub_C 1),
    monic_X.normalize_eq_self, (monic_X_sub_C 1).normalize_eq_self]
  simp [pow_two, mul_assoc]

-- At N = 2 the degree cutoff can include one linear prime but excludes X.
example :
    |∑ᶠ r ∈ {r : (ZMod 2)[X] | r.Monic ∧ (kappaPow exponents r).natDegree ≤ 2},
      (moebius r : ℝ) * ∑ᶠ f ∈ {f : (ZMod 2)[X] | f.Monic ∧ f ∣ kappaPow exponents r},
        ∑ᶠ ℓ ∈ {ℓ : (ZMod 2)[X] | ℓ.Monic ∧ ℓ ∣ f}, (moebius ℓ : ℝ)| ≤ 2 := by
  have h := abs_sum_moebius_kappaPow_le exponents (fun p _ _ ↦ two_le_exponents p)
    (N := 2) (by decide)
  simpa [minimum_eq_two, ZMod.card, show (2 : ℝ) / 2 = 1 by norm_num] using h

end MetaMathlibExt.abs_sum_moebius_kappaPow_le

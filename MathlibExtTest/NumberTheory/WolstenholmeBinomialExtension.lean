/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WolstenholmeBinomialExtension

/-! # Tests for binomial extensions of Wolstenholme's theorem -/

open MetaMathlibExt

-- At the diagonal, the shifted numerator and denominator have identical factors.
example (p m : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    (1 : ℚ) = (∏ j ∈ Finset.range m, (((j + 1) * p - 1).choose (p - 1) : ℚ)) /
      ∏ j ∈ Finset.range m, (((j + 1) * p - 1).choose (p - 1) : ℚ) := by
  simpa only [Nat.sub_self, Nat.zero_add, Nat.choose_self, Nat.cast_one, one_mul] using
    (choose_mul_prime_eq_prod_div_prod p m m hp hm le_rfl).1

-- With two blocks at the smallest prime, both denominator products exceed one.
example : (70 : ℚ) = 6 * (5 * 7) / (1 * 3) ∧ (70 : ℚ) = (15 * 28) / (1 * 6) := by
  have h := choose_mul_prime_eq_prod_div_prod 2 2 4 Nat.prime_two (by decide) (by decide)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at h
  exact h

-- For two blocks at p = 3, check both cleared-denominator expressions independently.
example : (9 : ℕ).choose 6 * (∏ j ∈ Finset.range 2, (j * 3 + 1).ascFactorial 2) = 3360 ∧
    (3 : ℕ).choose 2 * (∏ j ∈ Finset.range 2, ((1 + j) * 3 + 1).ascFactorial 2) = 3360 :=
  by decide

example : (9 : ℕ).choose 6 * (∏ j ∈ Finset.range 2, (j * 3 + 1).ascFactorial 2) =
    (3 : ℕ).choose 2 * (∏ j ∈ Finset.range 2, ((1 + j) * 3 + 1).ascFactorial 2) :=
  choose_mul_prod_ascFactorial 3 1 2 Nat.prime_three (by decide)

-- For the first derivative of a quadratic term over ℚ₂, the multiplier is two.
example (x : ℚ_[2]) : ‖x + x‖ ≤ ‖x‖ := by
  simpa only [Nat.choose_one_right, add_nsmul, one_nsmul] using
    (norm_choose_nsmul_coeff_le (p := 2) (fun _ => x) ‖x‖ (fun _ => le_rfl) 1 1)

-- The upper index can be zero for any admissible lower index.
example (p k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) : Ring.choose (0 : ℤ) (k * p) = 0 := by
  simpa using (ringChoose_neg_mul_mul_eq p 0 k hp hk).2

-- At p = 1 and odd lower index, the sign is negative and the ratio is nonintegral.
example : Ring.choose (-2 : ℤ) 3 = -4 := by
  have h := (ringChoose_neg_mul_mul_eq 1 2 3 (by decide) (by decide)).1
  norm_num [Nat.choose] at h
  exact_mod_cast h

open Polynomial

-- At composite p, the two factors contribute 1 and 70 to the coefficient of X^4.
example : (((X + 1 : ℕ[X]) ^ 8 * (X ^ 4 + 1)).coeff 4) = 71 := by
  have h := coeff_add_one_pow_mul_X_pow_add_one_pow 4 3 2 1 (by decide)
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  exact h

-- With n < j, the second factor has exponent zero, also when p = 1.
example : ((X + 1 : ℕ[X]) ^ 2).coeff 1 = 2 := by
  have h := coeff_add_one_pow_mul_X_pow_add_one_pow 1 1 2 1 (by decide)
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  exact h

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WolstenholmeBinomialExtension

/-! # Tests for the two product formulas for binomial coefficients at prime multiples -/

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

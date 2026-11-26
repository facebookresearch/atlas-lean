/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.GcdSumMeanSquare

open MetaMathlibExt Complex

-- The value at zero agrees with the convention in the definition.
example : gcdSumMean 0 = 0 := by simp [gcdSumMean]

-- The exponent-zero case gives the unit even though the prime is arbitrary.
example {p : ℕ} (hp : p.Prime) : gcdSumMean (p ^ 0) = 1 := by
  rw [gcdSumMean_prime_pow hp]
  norm_num

-- Combine the repeated prime factor of 12 with its coprime factor 3.
example : gcdSumMean 12 = 10 / 3 := by
  rw [show 12 = 2 ^ 2 * 3 ^ 1 by decide, gcdSumMean_mul_of_coprime (by decide),
    gcdSumMean_prime_pow Nat.prime_two, gcdSumMean_prime_pow Nat.prime_three]
  norm_num

-- A repeated prime divisor contributes twice to the mean.
example : gcdSumMean 4 = 2 := by
  rw [gcdSumMean, show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]
  norm_num

-- The same correction series converges inside the strip and gives the identity to its right.
example : ∃ h : ℕ → ℂ, LSeriesSummable h (1 / 4 + I) ∧
    LSeries (fun n => ((gcdSumMean n ^ 2 : ℝ) : ℂ)) (2 + I) =
      riemannZeta (2 + I) ^ 4 / riemannZeta (2 * (2 + I)) * LSeries h (2 + I) := by
  obtain ⟨h, hsum, heq⟩ := LSeries_gcdSumMean_sq_eq_riemannZeta_pow_four_div
  exact ⟨h, hsum _ (by norm_num), heq _ (by norm_num)⟩

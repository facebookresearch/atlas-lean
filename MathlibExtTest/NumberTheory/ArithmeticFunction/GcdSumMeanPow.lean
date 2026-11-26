/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.GcdSumMeanPow

open MetaMathlibExt Complex

-- For `k = 2` the exponents are `2 ^ 2 = 4` and `4 ^ 2 - 3 ^ 2 - (2 ^ 2).choose 2 = 1`, as in the
-- factorization `ζ(s) ^ 4 / ζ(2s)` of the series of the squared mean.
example : ∃ g h : ℕ → ℂ,
    LSeries (fun n => ((gcdSumMean n ^ 2 : ℝ) : ℂ)) (2 + I) =
        riemannZeta (2 + I) ^ 4 * LSeries g (2 + I) ∧
      LSeries g (2 + I) * riemannZeta (2 * (2 + I)) = LSeries h (2 + I) := by
  obtain ⟨g, h, -, -, H⟩ := LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul 2
  obtain ⟨h₁, h₂⟩ := H (2 + I) (by norm_num)
  rw [show 2 ^ 2 = 4 by norm_num] at h₁
  rw [show 4 ^ 2 - 3 ^ 2 - (2 ^ 2 : ℕ).choose 2 = 1 by decide, pow_one] at h₂
  exact ⟨g, h, h₁, h₂⟩

-- For `k = 0` the series is `ζ(s)` times `G_0(s)`, and the exponent of `ζ(2s)` vanishes, so the
-- two correction series have the same sum.
example : ∃ g h : ℕ → ℂ,
    LSeries (fun n => ((gcdSumMean n ^ 0 : ℝ) : ℂ)) 2 = riemannZeta 2 * LSeries g 2 ∧
      LSeries g 2 = LSeries h 2 := by
  obtain ⟨g, h, -, -, H⟩ := LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul 0
  obtain ⟨h₁, h₂⟩ := H 2 (by norm_num)
  rw [show 2 ^ 0 = 1 by norm_num, pow_one] at h₁
  rw [show 4 ^ 0 - 3 ^ 0 - (2 ^ 0 : ℕ).choose 2 = 0 by decide, pow_zero, mul_one] at h₂
  exact ⟨g, h, h₁, h₂⟩

-- The second correction series converges inside the strip `1/3 < Re s ≤ 1/2`, where the first
-- one is not claimed to converge, and it is the same series that the factorization gives at
-- `2 + I`.
example (k : ℕ) : ∃ g h : ℕ → ℂ, LSeriesSummable h (2 / 5 + I) ∧
    LSeries (fun n => ((gcdSumMean n ^ k : ℝ) : ℂ)) (2 + I) =
        riemannZeta (2 + I) ^ (2 ^ k) * LSeries g (2 + I) ∧
      LSeries g (2 + I) * riemannZeta (2 * (2 + I)) ^ (4 ^ k - 3 ^ k - (2 ^ k).choose 2) =
        LSeries h (2 + I) := by
  obtain ⟨g, h, -, hh, H⟩ := LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul k
  exact ⟨g, h, hh _ (by norm_num), H (2 + I) (by norm_num)⟩

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CentralBinomDigammaSeries
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Special values of the central binomial and cotangent series -/

namespace MetaMathlibExt.CentralBinomDigammaSeries

-- At h = 1/2 the Euler constants cancel and the sine denominator is one.
example :
    ∑' n : ℕ, (4 : ℂ) ^ n *
        (Complex.Gamma (3 / 2) * Complex.Gamma (n + 1 / 2) / n.factorial) /
        (((n + 1).centralBinom : ℂ) * ((n : ℂ) + 1) ^ 2) =
      Real.pi * Complex.log 2 / 2 := by
  have hh (m : ℕ) : (1 / 2 : ℂ) ≠ m := by
    intro h
    have he : (1 : ℂ) = 2 * (m : ℂ) := by linear_combination 2 * h
    have : 1 = 2 * m := by exact_mod_cast he
    omega
  have h := tsum_four_pow_div_binom_mul_centralBinom_mul_sq hh (by norm_num)
  rw [show (1 / 2 + 1 / 2 : ℂ) = 1 by norm_num, Complex.digamma_one,
    Complex.digamma_one_half, mul_one_div, Complex.sin_pi_div_two] at h
  rw [show (1 / 2 + 1 : ℂ) = 3 / 2 by norm_num] at h
  simp_rw [show ∀ n : ℕ, (n : ℂ) - 1 / 2 + 1 = n + 1 / 2 from fun n ↦ by ring] at h
  rw [h]
  ring

-- The endpoint k = 2 evaluates to zero.
example :
    ((2 : ℝ) - 2) * (1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) *
        ∏ j ∈ Finset.Icc 1 (n + 1), (2 * (j : ℝ) - (2 - 2)) / (2 * j + 1)) = 0 :=
  (sub_two_mul_one_add_tsum_prod_eq_pi_mul_cot (k := 2) (by decide)).trans <| by
    norm_num [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two]

-- The first positive-prefactor case is the paper's series for π / √3.
example :
    1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) *
        ∏ j ∈ Finset.Icc 1 (n + 1), (3 * (j : ℝ) - 1) / (3 * j + 1) =
      Real.pi / Real.sqrt 3 := by
  have hcot : Real.cot (Real.pi / 3) = 1 / Real.sqrt 3 := by
    rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
    field_simp
  have h₁ : (3 : ℝ) - 2 = 1 := by norm_num
  simpa only [Nat.cast_ofNat, h₁, one_mul, hcot, mul_one_div] using
    sub_two_mul_one_add_tsum_prod_eq_pi_mul_cot (k := 3) (by decide)

end MetaMathlibExt.CentralBinomDigammaSeries

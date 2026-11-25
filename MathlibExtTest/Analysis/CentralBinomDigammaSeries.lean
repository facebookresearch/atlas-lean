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

/-! # The central binomial digamma series at one half -/

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

end MetaMathlibExt.CentralBinomDigammaSeries

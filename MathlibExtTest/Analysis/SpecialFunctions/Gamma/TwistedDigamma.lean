/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.TwistedDigamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex MetaMathlibExt

namespace MetaMathlibExt.TwistedDigammaTest

private theorem four_terms {k : ℕ} (hk : 1 ≤ k) (hk' : k < 4) {z : ℂ}
    (hz : exp (2 * Real.pi * I * k / 4) = z) :
    z * digamma (1 / 4) + z ^ 2 * digamma (1 / 2) + z ^ 3 * digamma (3 / 4) +
      z ^ 4 * digamma 1 = 4 * log (1 - z) := by
  have h := sum_exp_mul_digamma_div_eq_mul_log_one_sub hk hk'
  have hterm (a : ℕ) : exp (2 * Real.pi * I * k * a / 4) = z ^ a := by
    rw [← hz, ← exp_nat_mul]
    congr 1
    ring
  simp_rw [Nat.cast_ofNat, hterm, hz] at h
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide] at h
  norm_num [Finset.sum_insert] at h ⊢
  linear_combination h

-- A nonprimitive twist at a composite denominator has order two.
example :
    digamma (1 / 2) + digamma 1 - digamma (1 / 4) - digamma (3 / 4) = 4 * log 2 := by
  have hz : exp (2 * Real.pi * I * (2 : ℕ) / 4) = -1 := by
    convert exp_pi_mul_I using 2
    push_cast
    ring
  have h := four_terms (k := 2) (by decide) (by decide) hz
  norm_num at h ⊢
  linear_combination h

-- The positive frequency at the same denominator gives the principal log of 1 - i.
example :
    I * digamma (1 / 4) - digamma (1 / 2) - I * digamma (3 / 4) + digamma 1 =
      4 * log (1 - I) := by
  have hz : exp (2 * Real.pi * I * (1 : ℕ) / 4) = I := by
    convert exp_pi_div_two_mul_I using 2
    push_cast
    ring
  have h := four_terms (k := 1) (by decide) (by decide) hz
  simpa [pow_succ, I_mul_I, sub_eq_add_neg] using h

end MetaMathlibExt.TwistedDigammaTest

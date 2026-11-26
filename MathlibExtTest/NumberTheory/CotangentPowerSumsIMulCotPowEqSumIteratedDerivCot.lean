/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CotangentPowerSumsIMulCotPowEqSumIteratedDerivCot
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp

/-! # Tests for `MathlibExt.NumberTheory.CotangentPowerSumsIMulCotPowEqSumIteratedDerivCot` -/

namespace MathlibExtTest.NumberTheory.CotangentPowerSumsIMulCotPowEqSumIteratedDerivCot

open MetaMathlibExt

-- At `r = 1` the sum has a single term with `c_{1,1} = 1`.
example (x : ℝ) (hx : Real.sin x ≠ 0) :
    (Complex.I * (Real.cot x : ℂ)) ^ 1 = Complex.I * (Real.cot x : ℂ) := by
  have h := I_mul_cot_pow_eq_sum_iteratedDeriv_cot 1 le_rfl x hx
  rw [Finset.Icc_self, Finset.sum_singleton, show (1 : ℕ) - 1 = 0 by decide,
    iteratedDeriv_zero, cotangentPowerCoeff_one_one] at h
  linear_combination h

-- At `r = 2` the identity recovers `(i cot x)^2 = -cot x ^ 2`, using `c_{2,1} = 0`,
-- `c_{2,2} = -1` and the derivative of `cot`.
example (x : ℝ) (hx : Real.sin x ≠ 0) :
    (Complex.I * (Real.cot x : ℂ)) ^ 2 = -((Real.cot x : ℂ)) ^ 2 := by
  have hderiv : iteratedDeriv 1 Real.cot x = -(1 + Real.cot x ^ 2) := by
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    have h : HasDerivAt Real.cot (-(1 + Real.cot x ^ 2)) x := by
      rw [show Real.cot = fun y => Real.cos y / Real.sin y from
        funext Real.cot_eq_cos_div_sin]
      convert (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx using 1
      field_simp
      ring
    exact h.deriv
  have hc21 : cotangentPowerCoeff 2 1 = 0 :=
    cotangentPowerCoeff_eq_zero_of_mod_two_ne (by decide) (by decide) (by decide)
  have hc22 : cotangentPowerCoeff 2 2 = -1 := cotangentPowerCoeff_two_two
  have hI : (Complex.I)^2 = -1 := by rw [pow_two, Complex.I_mul_I]
  have h := I_mul_cot_pow_eq_sum_iteratedDeriv_cot 2 (by decide) x hx
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by decide : (1:ℕ) ≠ 2),
    show (1 : ℕ) - 1 = 0 by decide, show (2 : ℕ) - 1 = 1 by decide,
    iteratedDeriv_zero, hderiv, hc21, hc22] at h
  push_cast at h ⊢
  rw [hI] at h
  linear_combination h

end MathlibExtTest.NumberTheory.CotangentPowerSumsIMulCotPowEqSumIteratedDerivCot

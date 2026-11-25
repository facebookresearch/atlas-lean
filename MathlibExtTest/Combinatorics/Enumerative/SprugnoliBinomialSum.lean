/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SprugnoliBinomialSum
import Mathlib.Tactic.NormNum

/-! # Tests for Sprugnoli's binomial sum theorem -/

open PowerSeries MetaMathlibExt

-- If x > n, no term contributes, even for a series with nonzero constant coefficient.
example (f : PowerSeries ℂ) :
    coeff 1 (X ^ 2 * ((1 - X : PowerSeries ℂ) ^ 3)⁻¹ * f.subst (X * (1 - X)⁻¹)) = 0 := by
  have h := (sum_choose_mul_coeff_eq_coeff_subst 1 2 0 1 0 1 (by decide) (by decide) 0 0 f).1.symm
  simpa [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt] using h

private noncomputable def f : PowerSeries ℂ := 1 + C 2 * X + C 5 * X ^ 2

-- With positive a and b - a > 1, the linear term lands exactly on degree three,
-- whereas the nonzero quadratic coefficient contributes nothing.
example :
    coeff 3 (X * ((1 - X : PowerSeries ℂ) ^ 2)⁻¹ * f.subst (X ^ 2 * ((1 - X) ^ 3)⁻¹)) = 5 := by
  have h := (sum_choose_mul_coeff_eq_coeff_subst 3 1 1 3 0 1 (by decide) (by decide) 0 0 f).1.symm
  norm_num [f, Finset.sum_range_succ, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow,
    Nat.choose_succ_succ] at h
  exact h

-- For c = 2, the k = 1 term contributes at the exact cutoff m = 2.
example (g : PowerSeries ℂ) :
    coeff 2 (g.subst (X ^ 2 * binomialSeries ℂ (-2 : ℂ))) = coeff 1 g := by
  have h := (sum_choose_mul_coeff_eq_coeff_subst 0 0 0 1 2 2 (by decide) (by decide) 0 (-2) g).2.symm
  norm_num [Finset.sum_range_succ, Ring.choose_zero_ite] at h
  exact h

-- The surviving k = 1 term combines the exponents 1 and -3; k = 2 is beyond degree three.
example :
    coeff 3 (binomialSeries ℂ (1 : ℂ) * f.subst (X ^ 2 * binomialSeries ℂ (-3 : ℂ))) = -4 := by
  have h := (sum_choose_mul_coeff_eq_coeff_subst 0 0 0 1 3 2 (by decide) (by decide) 1 (-3) f).2.symm
  have hchoose : Ring.choose (1 : ℂ) 3 = 0 := by
    rw [← Nat.cast_one (R := ℂ), Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by decide),
      Nat.cast_zero]
  norm_num [f, Finset.sum_range_succ, hchoose, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow] at h
  exact h

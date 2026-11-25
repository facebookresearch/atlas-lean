/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MinusculePolynomialClosedForm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MetaMathlibExt Polynomial

-- At n = 0 the polynomial N_0 vanishes, so the right-hand side of the closed form vanishes too.
example : C (2 * (((0 : ℕ) : ℚ) + 1)) * X * ((1 + X) ^ (2 * 0) + (1 - X) ^ (2 * 0)) -
    ((1 + X) ^ (2 * 0 + 2) - (1 - X) ^ (2 * 0 + 2)) = (0 : ℚ[X]) := by
  rw [← minusculePolynomialA_comp_sq]
  simp [minusculePolynomialA]

-- The factor 16x is not a zero divisor, so the closed form determines N_n(x^2): at n = 2 it
-- gives 2x^2, as N_2 = 2x predicts.
example : (minusculePolynomialA 2).comp (X ^ 2) = C 2 * X ^ 2 := by
  have h16 : (C 16 * X : ℚ[X]) ≠ 0 := mul_ne_zero (C_ne_zero.mpr (by norm_num)) X_ne_zero
  refine mul_left_cancel₀ h16 ?_
  rw [minusculePolynomialA_comp_sq]
  simp only [Nat.cast_ofNat, map_mul, map_add, map_one, map_ofNat]
  ring

-- Evaluating at x = 1, where 1 - x vanishes, gives 16 N_3(1) = 8 * 4^3 - 4^4, so N_3(1) = 16.
example : (minusculePolynomialA 3).eval 1 = 16 := by
  have h := congrArg (eval 1) (minusculePolynomialA_comp_sq 3)
  simp only [eval_mul, eval_C, eval_X, eval_comp, eval_pow, eval_sub, eval_add, eval_one]
    at h
  norm_num at h
  linarith

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EulerPolynomialFormulasEulerPolyHalfEqSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Boundary cases for Euler polynomials at `(x + 1)/2` -/

namespace MathlibExtTest.NumberTheory.EulerPolynomialFormulasEulerPolyHalfEqSum

open Polynomial MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

-- At degree zero both sides reduce to the constant polynomial one.
example : (2 : ℚ) ^ 0 • (eulerPoly 0).comp (C (1 / 2) * (X + 1)) = 1 := by
  have h0 : eulerAlpha 0 = 1 := rfl
  rw [eulerPoly_half_eq_sum 0]
  norm_num [Finset.sum_range_succ, genStirlingPoly, h0]

-- At degree one both sides reduce to `X`.
example (x : ℚ) :
    (((2 : ℚ) ^ 1 • (eulerPoly 1).comp (C (1 / 2) * (X + 1)))).eval x = x := by
  have h0 : eulerAlpha 0 = 1 := rfl
  have h1 : eulerAlpha 1 = 0 := rfl
  rw [eulerPoly_half_eq_sum 1]
  norm_num [Finset.sum_range_succ, genStirlingPoly, h0, h1, eval_smul, smul_eq_mul]

-- At degree two the weight `eulerAlpha 2 = -1/2` is nonzero and both sides reduce to `X² - 1`.
example : (2 : ℚ) ^ 2 • (eulerPoly 2).comp (C (1 / 2) * (X + 1)) = X ^ 2 - 1 := by
  have h0 : eulerAlpha 0 = 1 := rfl
  have h1 : eulerAlpha 1 = 0 := rfl
  have h2 : eulerAlpha 2 = -1 / 2 := by norm_num [eulerAlpha]
  rw [eulerPoly_half_eq_sum 2]
  apply Polynomial.funext
  intro x
  norm_num [Finset.sum_range_succ, genStirlingPoly, h0, h1, h2, eval_smul, smul_eq_mul]
  ring

end MathlibExtTest.NumberTheory.EulerPolynomialFormulasEulerPolyHalfEqSum

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EulerPolynomialFormulasDoubleSum
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Coefficient and low-degree checks for the Euler polynomial double sum -/

open Polynomial MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

-- The product on the generating-function side has zero quadratic coefficient.
example : PowerSeries.coeff 2
    (PowerSeries.mk eulerAlpha * (2 + 2 * PowerSeries.X + PowerSeries.X ^ 2)) = 0 := by
  rw [eulerAlpha_gf_and_closed_form.1]
  have h : (2 + 2 * PowerSeries.X : PowerSeries ℚ) =
      PowerSeries.C 2 + PowerSeries.C 2 * PowerSeries.X := by
    simp only [map_ofNat]
  rw [h]
  norm_num [PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]

-- The degree-three closed form has several nonzero summands, with mixed signs.
example : eulerAlpha 3 = 1 / 2 := by
  rw [eulerAlpha_gf_and_closed_form.2 3]
  norm_num [Finset.sum_range_succ, Nat.choose_succ_succ]

-- Degree zero reduces both sums to their first terms.
example : eulerPoly 0 = 1 := by
  rw [← one_smul ℚ (eulerPoly 0), ← pow_zero (2 : ℚ), eulerPoly_eq_double_sum]
  apply Polynomial.funext
  intro x
  norm_num [genStirlingPoly_eval, eval_smul, smul_eq_mul]

-- Degree two exercises the mixed index `k = ℓ = 1`.
example : (2 : ℚ) ^ 2 • eulerPoly 2 = (C 2 * X - 1) ^ 2 - 1 := by
  rw [eulerPoly_eq_double_sum]
  apply Polynomial.funext
  intro x
  norm_num [Finset.sum_range_succ, genStirlingPoly_eval, Nat.factorial_succ, eval_smul, smul_eq_mul]
  ring

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EulerPolynomialFormulasDoubleSum
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Low-degree cases of the double-sum formula for Euler polynomials -/

open Polynomial MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

-- Degree zero reduces both sums to their first terms.
example : eulerPoly 0 = 1 := by
  rw [← one_smul ℚ (eulerPoly 0), ← pow_zero (2 : ℚ), eulerPoly_eq_double_sum]
  norm_num [genStirlingPoly]

-- Degree two exercises the mixed index `k = ℓ = 1`.
example : (2 : ℚ) ^ 2 • eulerPoly 2 = (C 2 * X - 1) ^ 2 - 1 := by
  rw [eulerPoly_eq_double_sum]
  apply Polynomial.funext
  intro x
  norm_num [Finset.sum_range_succ, genStirlingPoly, Nat.factorial_succ, eval_smul, smul_eq_mul]
  ring

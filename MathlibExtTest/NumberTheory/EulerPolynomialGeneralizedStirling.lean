/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EulerPolynomialGeneralizedStirling
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Low-degree cases of the generalized Stirling expansion of Euler polynomials -/

open Polynomial MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

-- Degree one is the first degree covered by the theorem.
example : (2 : ℚ) • eulerPoly 1 = C 2 * X - 1 := by
  rw [← pow_one (2 : ℚ), eulerPoly_eq_sum_genStirling 1 (by decide)]
  norm_num [Finset.sum_range_succ, genStirlingPoly, eulerAlpha]

-- Degree two includes the nonzero coefficient `eulerAlpha 2`.
example : (2 : ℚ) ^ 2 • eulerPoly 2 = (C 2 * X - 1) ^ 2 - 1 := by
  rw [eulerPoly_eq_sum_genStirling 2 (by decide)]
  apply Polynomial.funext
  intro x
  norm_num [Finset.sum_range_succ, genStirlingPoly, eulerAlpha, eval_smul, smul_eq_mul]
  ring

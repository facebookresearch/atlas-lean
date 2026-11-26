/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EulerPolynomialBinomialAverage
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Boundary cases for the binomial average of Euler polynomials -/

open Polynomial MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

-- At degree zero the alternating outer weights sum to one.
example : eulerPoly 0 = 1 := by
  rw [eulerPoly_eq_binomial_average 2 0 (hn := by decide)]
  apply Polynomial.funext
  intro x
  norm_num [Finset.sum_range_succ, Nat.choose, eval_smul, smul_eq_mul]

-- The last admissible degree at the smallest admissible order gives the fifth Euler polynomial.
example (x : ℚ) : (eulerPoly 5).eval x = x ^ 5 - 5 / 2 * x ^ 4 + 5 / 2 * x ^ 2 - 1 / 2 := by
  rw [eulerPoly_eq_binomial_average 2 5 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose, eval_smul, smul_eq_mul]
  ring

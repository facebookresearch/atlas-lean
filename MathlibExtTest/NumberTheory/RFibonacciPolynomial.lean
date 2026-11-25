/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RFibonacciPolynomial
import Mathlib.Tactic.NormNum

/-! # Tests for separability of the (-r)-Fibonacci characteristic polynomial -/

open Polynomial MetaMathlibExt

-- At the least allowed index and with zero constant term, the roots are 0 and 1.
example : (X ^ 2 - X : ℚ[X]).Separable := by
  simpa using separable_negRFibonacci_charPoly (r := 1) (by decide) (0 : ℚ) 1 (by norm_num)

-- The excluded parameters give a cubic with a common root of the polynomial and its derivative.
example : (2 + 1 : ℚ) ^ 3 * (-2 / 3) ^ 2 * (1 / 3) = 2 ^ 2 ∧
    ¬ (X ^ 3 - 3 * X - 2 : ℚ[X]).Separable := by
  refine ⟨by norm_num, fun h => ?_⟩
  have hroot := aeval_ne_zero_of_isCoprime h (-1 : ℚ)
  norm_num at hroot

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RFibonacciPolynomialNegRFibonacciEqSumRoots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the Binet formula for negative-order Fibonacci polynomials

The rational roots -1, 0 and 1 give a concrete instance with a zero denominator.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 9 (`integers-2025-A38-thm-9`).
-/

namespace MathlibExtTest.NumberTheory.RFibonacciPolynomialNegRFibonacciEqSumRoots

example : MetaMathlibExt.negRFibonacci 2 (0 : ℚ) 1 4 = 0 := by
  have h := MetaMathlibExt.negRFibonacci_eq_sum_roots (K := ℚ) (r := 2)
    (by decide) 0 1 ![-1, 0, 1] (by decide)
    (by simp [Fin.prod_univ_succ]; ring) 3
  convert h using 1; norm_num [Fin.sum_univ_succ]

-- With `r = 2`, `x = 6/7` and `y = 1/7` the characteristic polynomial `X^3 - 7X + 6` has roots
-- `-3, 1, 2`, so `x y⁻¹ = 6` contributes to every denominator; at `n = 3` the formula gives `-6`.
example : MetaMathlibExt.negRFibonacci 2 (6 / 7 : ℚ) (Units.mk0 (1 / 7) (by norm_num)) 4 = -6 := by
  have h := MetaMathlibExt.negRFibonacci_eq_sum_roots (K := ℚ) (r := 2)
    (by decide) (6 / 7) (Units.mk0 (1 / 7) (by norm_num)) ![-3, 1, 2] (by decide)
    (by apply Polynomial.funext; intro t; simp [Fin.prod_univ_succ]; ring) 3
  rw [h]; norm_num [Fin.sum_univ_succ]

end MathlibExtTest.NumberTheory.RFibonacciPolynomialNegRFibonacciEqSumRoots

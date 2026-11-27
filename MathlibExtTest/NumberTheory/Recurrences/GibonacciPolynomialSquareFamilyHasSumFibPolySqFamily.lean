/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialSquareFamilyHasSumFibPolySqFamily

/-! # Tests for the Fibonacci polynomial square family sum -/

namespace MathlibExtTest.NumberTheory.Recurrences.GibonacciPolynomialSquareFamilyHasSumFibPolySqFamily

open Polynomial
open MetaMathlibExt

local notation "F" => fun n : ℕ => aeval (1 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)

-- At `x = 1` the Fibonacci polynomials are the Fibonacci numbers; the `k = p = r = t = 1`
-- instance sums to `(1 - √5) / 2`.
example : ∑' n : ℕ, (-1 : ℝ) / (F (2 * (n + 1)) ^ 2 + 1) = (1 - √5) / 2 := by
  have h := (hasSum_fibPoly_sq_family (x := 1) zero_lt_one (k := 1) (p := 1) (r := 1) (t := 1)
    (by decide) (by decide) (by decide) (by decide)).tsum_eq
  norm_num [generalizedFibonacciPolynomial] at h
  rw [h]
  ring

end MathlibExtTest.NumberTheory.Recurrences.GibonacciPolynomialSquareFamilyHasSumFibPolySqFamily

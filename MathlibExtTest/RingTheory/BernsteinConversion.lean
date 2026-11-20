/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.RingTheory.Polynomial.BernsteinConversion
import Mathlib.Tactic.NormNum

-- The conversion applies outside the unit interval as well as at endpoints.
example : ∑ ν ∈ Finset.range 4, ((ν.choose 2 : ℝ) / (3 : ℕ).choose 2) *
    (bernsteinPolynomial ℝ 3 ν).eval (-2) = 4 := by
  convert bernsteinPolynomial.monomial_bernstein 3 2 (by decide) (-2) using 1
  norm_num

example (s : ℝ) : ∑ ν ∈ Finset.range 1, ((ν.choose 0 : ℝ) / (0 : ℕ).choose 0) *
    (bernsteinPolynomial ℝ 0 ν).eval s = 1 := by
  simpa using bernsteinPolynomial.monomial_bernstein 0 0 le_rfl s

#print axioms bernsteinPolynomial.choose_bernstein_sum
#print axioms bernsteinPolynomial.monomial_bernstein

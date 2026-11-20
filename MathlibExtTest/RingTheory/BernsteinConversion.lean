/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.RingTheory.Polynomial.BernsteinConversion
import Mathlib.Tactic.ComputeDegree
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

open Polynomial bernsteinPolynomial

-- A mixed quadratic can be degree-elevated to the cubic Bernstein basis.
example : bernsteinCoeff 3 (X ^ 2 + 2 * X + 3 : Polynomial ℝ) 1 = 11 / 3 := by
  norm_num [bernsteinCoeff, Finset.sum_range_succ, coeff_add, coeff_X_pow, coeff_X]

example : (X ^ 2 + 2 * X + 3 : Polynomial ℝ) =
    ∑ j ∈ Finset.range 4,
      C (bernsteinCoeff 3 (X ^ 2 + 2 * X + 3) j) * bernsteinPolynomial ℝ 3 j := by
  apply eq_sum_bernstein
  compute_degree
  norm_num

-- The degree-zero and zero-polynomial cases use the same API.
example (c : ℝ) : bernsteinCoeff 0 (C c) 0 = c := by
  simp [bernsteinCoeff]

example (n j : ℕ) : bernsteinCoeff n (0 : Polynomial ℝ) j = 0 := by
  simp [bernsteinCoeff]

-- The polynomial identity evaluates correctly outside the unit interval.
example : (∑ j ∈ Finset.range 4,
    bernsteinCoeff 3 (X ^ 2 + 2 * X + 3) j *
      (bernsteinPolynomial ℝ 3 j).eval (-2)) = 3 := by
  rw [← eval_eq_sum_bernstein (p := X ^ 2 + 2 * X + 3)
    (n := 3) (by compute_degree; norm_num)]
  norm_num

#print axioms bernsteinPolynomial.eq_sum_bernstein

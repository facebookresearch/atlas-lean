/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialSquareFamilySums

/-! # Reciprocal sums of shifted Fibonacci and Lucas polynomial squares at `x = 3/2` -/

namespace MetaMathlibExt.tsum_gibonacciPoly_sq_sub_family

open Polynomial

local notation "F" => fun n : ℕ => aeval (3 / 2 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)
local notation "L" => fun n : ℕ => aeval (3 / 2 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

private theorem sqrt_discriminant : √((3 / 2 : ℝ) ^ 2 + 4) = 5 / 2 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

-- The odd starting index gives a negative Fibonacci numerator and adds the square term.
example : ∑' n : ℕ, (-3 / 2 : ℝ) / (F (2 * n + 2) ^ 2 + 1) = -1 / 2 := by
  have h := (tsum_gibonacciPoly_sq_sub_family (x := 3 / 2) (by norm_num)
    (k := 1) (p := 1) (r := 1) (t := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide)).1
  rw [sqrt_discriminant] at h
  norm_num [generalizedFibonacciPolynomial] at h ⊢
  exact h

-- The Catalan-constant form with the Fibonacci polynomials and `C = 1` gives the same sum.
example : ∑' n : ℕ, (-3 / 2 : ℝ) / (F (2 * n + 2) ^ 2 + 1) = -1 / 2 := by
  have h := (hasSum_gibonacciPoly_sq_sub_family_of_catalan (x := 3 / 2) (by norm_num)
    (generalizedFibonacciPolynomial 0 1 X 1) 1 (Or.inl rfl) (by simp)
    (k := 1) (p := 1) (r := 1) (t := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide)).tsum_eq
  rw [sqrt_discriminant] at h
  norm_num [generalizedFibonacciPolynomial] at h ⊢
  exact h

-- At t = 2p the Lucas sum starts at L₂, with a shift of two in the initial ratio.
example : ∑' n : ℕ, (-225 / 16 : ℝ) / (L (2 * n + 3) ^ 2 + 25 / 4) = -15 / 68 := by
  have h := (tsum_gibonacciPoly_sq_sub_family (x := 3 / 2) (by norm_num)
    (k := 1) (p := 1) (r := 2) (t := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)).2
  rw [sqrt_discriminant] at h
  norm_num [generalizedFibonacciPolynomial, map_ofNat] at h ⊢
  exact h

-- The Catalan-constant form with the Lucas polynomials and `C = -(x^2 + 4)` gives the convergence
-- of the same Lucas series, not only its value.
example : HasSum (fun n : ℕ => (-225 / 16 : ℝ) / (L (2 * n + 3) ^ 2 + 25 / 4)) (-15 / 68) := by
  have h := hasSum_gibonacciPoly_sq_sub_family_of_catalan (x := 3 / 2) (by norm_num)
    (generalizedFibonacciPolynomial 2 X X 1) (-((3 / 2) ^ 2 + 4)) (Or.inr rfl)
    (by norm_num [generalizedFibonacciPolynomial, map_ofNat])
    (k := 1) (p := 1) (r := 2) (t := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rw [sqrt_discriminant] at h
  norm_num [generalizedFibonacciPolynomial, map_ofNat] at h ⊢
  exact h

end MetaMathlibExt.tsum_gibonacciPoly_sq_sub_family

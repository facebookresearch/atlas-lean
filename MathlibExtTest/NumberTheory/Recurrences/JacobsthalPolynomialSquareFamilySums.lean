/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.RealSqrt
import MathlibExt.NumberTheory.Recurrences.JacobsthalPolynomialSquareFamilySums

/-! # Jacobsthal reciprocal sums at the classical parameter two -/

namespace MetaMathlibExt.tsum_jacobsthalPoly_sq_sub_family

open Polynomial

local notation "J" => fun n => aeval (2 : ℝ) (generalizedFibonacciPolynomial 0 1 1 X n)
local notation "j" => fun n => aeval (2 : ℝ) (generalizedFibonacciPolynomial 2 1 1 X n)

-- The odd starting index gives negative Jacobsthal summands.
example : ∑' n : ℕ, -(2 : ℝ) ^ (2 * n + 1) / (J (2 * n + 2) ^ 2 + 2 ^ (2 * n + 1)) = -1 := by
  have h := (tsum_jacobsthalPoly_sq_sub_family (x := 2) (by norm_num)
    (k := 1) (p := 1) (r := 1) (t := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide)).1
  norm_num [generalizedFibonacciPolynomial] at h ⊢
  exact h

-- At the endpoint t = 2p the Lucas denominator has a positive discriminant term.
example : ∑' n : ℕ, -9 * (2 : ℝ) ^ (2 * n + 2) /
    (j (2 * n + 3) ^ 2 + 9 * 2 ^ (2 * n + 2)) = -3 / 5 := by
  have h := (tsum_jacobsthalPoly_sq_sub_family (x := 2) (by norm_num)
    (k := 1) (p := 1) (r := 1) (t := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)).2
  norm_num [generalizedFibonacciPolynomial, map_ofNat] at h ⊢
  exact h

end MetaMathlibExt.tsum_jacobsthalPoly_sq_sub_family

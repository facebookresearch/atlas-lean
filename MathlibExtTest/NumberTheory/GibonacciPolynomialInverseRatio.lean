/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPolynomialInverseRatio

/-! # Concrete inverse-ratio sums at `x = 3/2`, where the roots are `2` and `-1/2` -/

namespace MetaMathlibExt.GibonacciPolynomialInverseRatio

open Polynomial

local notation "F" => fun n : ℕ => aeval (3 / 2 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)
local notation "L" => fun n : ℕ => aeval (3 / 2 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

private theorem sqrt_discriminant : √((3 / 2 : ℝ) ^ 2 + 4) = 5 / 2 := by
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

-- For Fibonacci polynomials the squared ratios start at (2/3)² and tend to (1/2)².
example : ∑' n : ℕ, (F (2 * n + 1) ^ 2 / F (2 * n + 1 + 1) ^ 2 -
    F (2 * n + 3) ^ 2 / F (2 * n + 3 + 1) ^ 2) = 7 / 36 := by
  have h := tsum_gibonacciPoly_pow_inv_ratio_telescope (x := 3 / 2) (by norm_num)
    (Or.inl rfl) (k := 1) (by decide) 1 2
  simp only [Nat.mul_one] at h
  rw [h, sqrt_discriminant]
  norm_num [generalizedFibonacciPolynomial]

-- On every third odd index the Lucas ratios start below their limit.
example : ∑' n : ℕ, (L ((2 * n + 1) * 3) / L ((2 * n + 1) * 3 + 1) -
    L ((2 * n + 3) * 3) / L ((2 * n + 3) * 3 + 1)) = -5 / 514 := by
  have h := tsum_gibonacciPoly_pow_inv_ratio_telescope (x := 3 / 2) (by norm_num)
    (Or.inr rfl) (k := 3) (by decide) 1 1
  simp only [pow_one] at h
  rw [h, sqrt_discriminant]
  norm_num [generalizedFibonacciPolynomial, map_ofNat]

end MetaMathlibExt.GibonacciPolynomialInverseRatio

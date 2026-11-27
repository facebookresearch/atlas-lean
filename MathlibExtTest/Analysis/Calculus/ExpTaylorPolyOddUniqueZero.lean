/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Calculus.ExpTaylorPolyOddUniqueZero

/-! # Tests for the real zero of odd exponential Taylor polynomials -/

open MathlibExt.Analysis.Calculus.ExpTaylorPolyOddUniqueZeroWanted

-- At the smallest allowed degree the unique zero is -1.
example (x : ℝ) (hx : ∑ k ∈ Finset.range 2, x ^ k / k.factorial = 0) : x = -1 := by
  apply (existsUnique_sum_pow_div_factorial_eq_zero_of_odd 1 (by decide) odd_one).unique hx
  norm_num [Finset.sum_range_succ]

-- The first nonlinear case has the prescribed cubic and factorial coefficients.
example : ∃! x : ℝ, 1 + x + x ^ 2 / 2 + x ^ 3 / 6 = 0 := by
  simpa [Finset.sum_range_succ, Nat.factorial] using
    existsUnique_sum_pow_div_factorial_eq_zero_of_odd 3 (by decide) (by decide)

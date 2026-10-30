/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.WeierstrassNowhereDifferentiable

open Real

/-- The Weierstrass function is continuous (Theorem III). -/
example : Continuous Real.weierstrassFun :=
  Real.continuous_weierstrassFun

/-- The Weierstrass function is bounded by `4 / 3` (Theorem III). -/
example (x : ℝ) : |Real.weierstrassFun x| ≤ 4 / 3 :=
  Real.weierstrassFun_abs_le x

/-- The defining series of the Weierstrass function is summable at `0`. -/
example : Summable (fun k : ℕ => cos (160 ^ k * 0) / (4 : ℝ) ^ k) :=
  Real.summable_weierstrassFun_terms 0

/-- The Weierstrass function is not differentiable at `0`. -/
example : ¬ DifferentiableAt ℝ Real.weierstrassFun 0 :=
  Real.weierstrassFun_nowhere_differentiable 0

/-- Slope blow-up at `c = 0`, `n = 0`: there is a point `y ≠ 0` with
`|y| < 3π` whose difference quotient has absolute value at least `1 / (117π)`. -/
example : ∃ y : ℝ, y ≠ 0 ∧ |y - 0| < 3 * π / (160 : ℝ) ^ 0 ∧
    |(Real.weierstrassFun y - Real.weierstrassFun 0) / (y - 0)| ≥
      (40 : ℝ) ^ 0 / (117 * π) :=
  Real.weierstrassFun_slope_lower_bound 0 0

#print axioms Real.weierstrassFun_nowhere_differentiable

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EllipticCurveNaiveHeightLowerBoundsNaiveHeightLtSqrtMulNaiveHeightXRpow

import Mathlib.Tactic.NormNum

/-!
# Tests for the naive height bound in terms of the x-coordinate

We apply the bound to an integral point and a point with nonintegral coordinates.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Lemma 4.
-/

namespace MathlibExtTest.NumberTheory
namespace EllipticCurveNaiveHeightLowerBoundsNaiveHeightLtSqrtMulNaiveHeightXRpow

open MetaMathlibExt

example : Height.mulHeight ![(1 : ℚ), 1, 1] < Real.sqrt 2 := by
  have hx : Height.mulHeight ![(1 : ℚ), 1] = 1 := by
    rw [← Height.mulHeight₁_eq_mulHeight, Rat.mulHeight₁_eq_max]
    norm_num
  simpa only [hx, Real.one_rpow, mul_one, Int.cast_one, abs_one,
    show (1 : ℝ) + 1 = 2 by norm_num] using
    naiveHeight_lt_sqrt_mul_naiveHeight_x_rpow 1 1 (by decide) (by decide)
    (by decide) 1 1 (by norm_num)

example : Height.mulHeight ![(1 / 4 : ℚ), 7 / 8, 1] <
    Real.sqrt 8 * (4 : ℝ) ^ ((3 : ℝ) / 2) := by
  have h := naiveHeight_lt_sqrt_mul_naiveHeight_x_rpow 7 1 (by decide) (by decide)
    (by decide) (1 / 4) (7 / 8) (by norm_num)
  convert h using 1
  norm_num [← Height.mulHeight₁_eq_mulHeight, Rat.mulHeight₁_eq_max]

end EllipticCurveNaiveHeightLowerBoundsNaiveHeightLtSqrtMulNaiveHeightXRpow
end MathlibExtTest.NumberTheory

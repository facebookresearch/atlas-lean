/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EllipticCurveNaiveHeightLowerBounds

/-!
# A nonintegral point on the curve with coefficients 1 and 26

The point `(1/4, -41/8)` has primitive projective coordinates `(2 : -41 : 8)`.
-/

example :
    Real.sqrt 679 ^ ((1 : ℝ) / 6) / 1.634 <
      Height.mulHeight ![(1 / 4 : ℚ), -41 / 8, 1] := by
  convert MetaMathlibExt.naiveHeight_gt_of_small_linear_coeff 1 26 (by decide) (by decide)
    (by
      rw [← Real.sqrt_eq_rpow, lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num),
        Real.lt_sqrt (by norm_num)]
      norm_num)
    (1 / 4) (-41 / 8) (by norm_num) (by norm_num) using 1
  norm_num

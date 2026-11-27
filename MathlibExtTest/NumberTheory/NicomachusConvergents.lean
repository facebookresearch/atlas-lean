/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NicomachusConvergents

open MathlibExt.NumberTheory.NicomachusGeneralizationWanted

-- The placeholder at index zero is excluded from the square-root formula.
example :
    (nicomachusAlpha 0 : ℝ) ≠
      (-1 + Real.sqrt (11 - 10 / (3 + 2 * (nicomachusU 0 : ℝ)))) / 2 := by
  have hu : nicomachusU 0 = 1 := by
    simp [nicomachusU, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  norm_num [nicomachusAlpha, hu]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

-- The first nontrivial convergent is `[1; 6, 3] = 22/19`.
example : (-1 + Real.sqrt (11 - 10 / (3 + 2 * (nicomachusU 2 : ℝ)))) / 2 = 22 / 19 := by
  rw [← nicomachusAlpha_eq 2 (hk := by norm_num)]
  norm_num [nicomachusAlpha]

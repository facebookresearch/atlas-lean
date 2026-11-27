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

-- The closed form gives zero for the empty interval, including the truncated triangular index.
example (k : ℕ) (hk : 1 ≤ k) :
    nicomachusTriangular (0 - 1) *
      ((1 + ((0 : ℕ) : ℝ)) * (2 - 3 * ((0 : ℕ) : ℝ) ^ 2) / (3 * (3 + 2 * (nicomachusU k : ℝ))) +
        (3 + 2 * ((0 : ℕ) : ℝ)) * nicomachusTriangular (0 - 1)) = 0 := by
  rw [← sum_quadratic_mul_quadratic_eq k hk 0]
  simp

-- At the second convergent, compute the first nonzero partial sum directly from the quadratics.
example :
    nicomachusTriangular (2 - 1) *
      ((1 + ((2 : ℕ) : ℝ)) * (2 - 3 * ((2 : ℕ) : ℝ) ^ 2) / (3 * (3 + 2 * (nicomachusU 2 : ℝ))) +
        (3 + 2 * ((2 : ℕ) : ℝ)) * nicomachusTriangular (2 - 1)) = 2525 / 361 := by
  rw [← sum_quadratic_mul_quadratic_eq 2 (by decide) 2]
  norm_num [nicomachusAlpha, show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_insert]

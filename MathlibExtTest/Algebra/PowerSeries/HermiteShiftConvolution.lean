/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.PowerSeries.HermiteShiftConvolution

/-! # Tests for the Hermite-shifted Catalan-type convolutions -/

open MetaMathlibExt PowerSeries

-- The kernel starts with coefficients 2, 10, 22. At exponent one, the two trinomials
-- are 1 - 2t + 3t² and 1 - 6t + t², so the quadratic coefficients differ.
example :
    let G : PowerSeries ℝ := (exp ℝ).subst (C 2 * X + C 3 * X ^ 2 : PowerSeries ℝ) *
      kampeDeFerietHermite 2 1 (C 2 + C 6 * X) (C 3)
    coeff 2 (G * trinomialNegPowSeries (-1) 1 2 3 2) = 8 ∧
      coeff 2 (G * trinomialNegPowSeries (-1) 1 6 1 2) = -36 := by
  have h := coeff_hermiteShift_mul_trinomialNegPowSeries 1 2 2 (-1) 2 3 3
  norm_num at h
  intro G
  constructor
  · rw [h.1, trinomialNegPowSeries_neg_one 2 3 (by decide)]
    norm_num [kampeDeFerietHermite, Finset.sum_range_succ, Nat.factorial, coeff_X,
      coeff_C_mul_X_pow]
  · rw [h.2, trinomialNegPowSeries_neg_one 6 1 (by decide)]
    norm_num [kampeDeFerietHermite, Finset.sum_range_succ, Nat.factorial, coeff_X,
      coeff_C_mul_X_pow]

-- At m = 0 only the repository's defined series is used, not an analytic expansion.
example (lam x y z : ℝ) :
    let G : PowerSeries ℝ := (exp ℝ).subst (C x * X + C y * X ^ 2 : PowerSeries ℝ) *
      kampeDeFerietHermite 2 2 (C x + C (2 * y) * X) (C y)
    constantCoeff (G * trinomialNegPowSeries lam 1 0 z 0) =
        (x ^ 2 + 2 * y) * constantCoeff (trinomialNegPowSeries lam 1 0 z 0) ∧
      constantCoeff (G * trinomialNegPowSeries lam 1 0 1 0) =
        (x ^ 2 + 2 * y) * constantCoeff (trinomialNegPowSeries lam 1 0 1 0) := by
  simpa [Finset.sum_range_succ, kampeDeFerietHermite_two_two] using
    coeff_hermiteShift_mul_trinomialNegPowSeries 2 0 0 lam x y z

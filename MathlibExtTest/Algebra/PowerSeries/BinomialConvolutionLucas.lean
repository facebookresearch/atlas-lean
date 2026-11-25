/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.PowerSeries.BinomialConvolutionLucas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the binomial square of the Lucas generating function -/

open MetaMathlibExt PowerSeries

-- For a = 2 and b = -1 the quadratic has a repeated root at 1.
example : binomialProduct ((2 : PowerSeries ℚ) * (1 - X)⁻¹) (2 * (1 - X)⁻¹) =
    2 * (1 - C (2 : ℚ) * X)⁻¹ + rescale 2 (2 * (1 - X)⁻¹) := by
  let g : PowerSeries ℚ := 2 * (1 - X)⁻¹
  have hD : (1 : PowerSeries ℚ) - C (2 : ℚ) * X - C (-1 : ℚ) * X ^ 2 =
      (1 - X) * (1 - X) := by
    simp only [map_ofNat, map_neg, map_one]
    ring
  have hg : g * (1 - C (2 : ℚ) * X - C (-1 : ℚ) * X ^ 2) = 2 - C (2 : ℚ) * X := by
    dsimp [g]
    rw [hD, ← mul_assoc, mul_assoc (2 : PowerSeries ℚ),
      PowerSeries.inv_mul_cancel _ (by simp), mul_one, map_ofNat]
    ring
  exact (binomialProduct_lucasV_generatingFunction (a := 2) (b := -1) (g := g) (hg := hg)).1

-- The denominator for a = 0 and b = 2 has a nonsplit reciprocal quadratic T² - 2 over ℚ.
-- Check n = 0, where the a^n term survives even though a = 0.
example : let g : PowerSeries ℚ := 2 * (1 - C (2 : ℚ) * X ^ 2)⁻¹
    coeff 0 g * coeff 0 g = 4 := by
  intro g
  have hg : g * (1 - C (0 : ℚ) * X - C (2 : ℚ) * X ^ 2) = 2 - C (0 : ℚ) * X := by
    simp only [map_zero, zero_mul, sub_zero, g, mul_assoc]
    rw [PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  have h0 : coeff 0 g = 2 := by
    change coeff 0 ((2 : PowerSeries ℚ) * (1 - C (2 : ℚ) * X ^ 2)⁻¹) = 2
    rw [← map_ofNat C, coeff_C_mul, coeff_zero_eq_constantCoeff_apply]
    simp
  have h := (binomialProduct_lucasV_generatingFunction (a := 0) (b := 2) (g := g) (hg := hg)).2 0
  simpa [h0, show (2 : ℚ) + 2 = 4 by norm_num] using h

/-- info: 'MetaMathlibExt.binomialProduct_lucasV_generatingFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms binomialProduct_lucasV_generatingFunction

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.SurfaceGravityWaves

/-!
# Dispersion-relation checks

Concrete consumers of `PhyslibExt.EarthScience.SurfaceGravityWaves`:
dispersion for a unit wave with `k = H = g = 1`, positivity of `ω²`,
and the deep-water limit `tanh → 1` in the form of a numeric bound.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`g = k = H = 1`, the frequency is `ω = √(tanh 1)`; the kinematic and
dynamic conditions are met with surface amplitude `1` and potential
amplitude `1 / √(tanh 1)`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit dispersion
- B. Positivity and a deep-water bound

## iv. References

- `PhyslibExt.EarthScience.SurfaceGravityWaves`
-/

/-- Unit dispersion: `ω = √(tanh 1)` satisfies `ω² = tanh 1`. -/
example : (Real.sqrt (Real.tanh 1)) ^ 2 = 1 * 1 * Real.tanh (1 * 1) := by
  simp only [mul_one, one_mul]
  exact Real.sq_sqrt (le_of_lt ((by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _))))

/-- The dispersion relation from the surface conditions, at `g = k = H = 1`,
`a = 1`, `b = 1 / √(tanh 1)`. -/
example : (Real.sqrt (Real.tanh 1)) ^ 2 = 1 * 1 * Real.tanh (1 * 1) := by
  have hT : 0 < Real.tanh 1 := (by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _))
  have hω : Real.sqrt (Real.tanh 1) ≠ 0 := Real.sqrt_ne_zero'.mpr hT
  have ha : (1 : ℝ) ≠ 0 := one_ne_zero
  have hkin : Real.sqrt (Real.tanh 1) * 1 =
      1 * Real.tanh (1 * 1) * (1 / Real.sqrt (Real.tanh 1)) := by
    have h1 : Real.tanh (1 * 1) = Real.tanh 1 := by rw [mul_one]
    rw [h1, mul_one, one_mul, mul_one_div, eq_div_iff hω]
    exact Real.mul_self_sqrt (le_of_lt hT)
  have hdyn : Real.sqrt (Real.tanh 1) * (1 / Real.sqrt (Real.tanh 1)) = 1 * 1 := by
    rw [mul_one]
    exact mul_one_div_cancel hω
  exact EarthScience.dispersion_from_surface_conditions
    (Real.sqrt (Real.tanh 1)) 1 1 1 1 (1 / Real.sqrt (Real.tanh 1)) hω ha hkin hdyn

/-- Positivity: with the same parameters, `0 < ω²`. -/
example : 0 < (Real.sqrt (Real.tanh 1)) ^ 2 := by
  have hT : 0 < Real.tanh 1 := (by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _))
  have hω : Real.sqrt (Real.tanh 1) ≠ 0 := Real.sqrt_ne_zero'.mpr hT
  have ha : (1 : ℝ) ≠ 0 := one_ne_zero
  have hkin : Real.sqrt (Real.tanh 1) * 1 =
      1 * Real.tanh (1 * 1) * (1 / Real.sqrt (Real.tanh 1)) := by
    have h1 : Real.tanh (1 * 1) = Real.tanh 1 := by rw [mul_one]
    rw [h1, mul_one, one_mul, mul_one_div, eq_div_iff hω]
    exact Real.mul_self_sqrt (le_of_lt hT)
  have hdyn : Real.sqrt (Real.tanh 1) * (1 / Real.sqrt (Real.tanh 1)) = 1 * 1 := by
    rw [mul_one]
    exact mul_one_div_cancel hω
  exact EarthScience.dispersion_positive (Real.sqrt (Real.tanh 1)) 1 1 1 1
    (1 / Real.sqrt (Real.tanh 1)) (by norm_num) (by norm_num) (by norm_num)
    hω ha hkin hdyn

/-- Deep water: the finite-depth factor `tanh 5` lies in `(0, 1)`, below
the deep-water limit `1`. -/
example : 0 < Real.tanh 5 ∧ Real.tanh 5 < 1 :=
  ⟨(by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _)), Real.tanh_lt_one 5⟩

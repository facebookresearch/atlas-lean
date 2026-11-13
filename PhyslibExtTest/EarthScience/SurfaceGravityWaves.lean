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
and a range check `0 < tanh 5 < 1` on the finite-depth factor.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`g = k = H = 1`, the frequency is `ω = √(tanh 1)`; the kinematic and
dynamic conditions are met with surface amplitude `tanh 1` and potential
amplitude `√(tanh 1)`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit dispersion
- B. Positivity and a range check

## iv. References

- `PhyslibExt.EarthScience.SurfaceGravityWaves`
-/

/-- Unit dispersion: `ω = √(tanh 1)` satisfies `ω² = tanh 1`. -/
example : (Real.sqrt (Real.tanh 1)) ^ 2 = 1 * 1 * Real.tanh (1 * 1) := by
  simp only [mul_one, one_mul]
  exact Real.sq_sqrt (le_of_lt ((by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _))))

/-- The dispersion relation from the surface conditions, at `g = k = H = 1`,
`a = tanh 1`, `b = √(tanh 1)`. -/
example : (Real.sqrt (Real.tanh 1)) ^ 2 = 1 * 1 * Real.tanh (1 * 1) := by
  have hT : 0 < Real.tanh 1 := (by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _))
  have hkin : Real.sqrt (Real.tanh 1) * Real.tanh 1 =
      1 * Real.tanh (1 * 1) * Real.sqrt (Real.tanh 1) := by
    rw [mul_one, one_mul, mul_comm]
  have hdyn : Real.sqrt (Real.tanh 1) * Real.sqrt (Real.tanh 1) = 1 * Real.tanh 1 := by
    rw [one_mul]
    exact Real.mul_self_sqrt hT.le
  exact EarthScience.dispersion_from_surface_conditions
    (Real.sqrt (Real.tanh 1)) 1 1 1 (Real.tanh 1) (Real.sqrt (Real.tanh 1)) hT.ne' hkin hdyn

/-- Positivity: with the same parameters, `0 < ω²`, with no `ω ≠ 0` fact
supplied. -/
example : 0 < (Real.sqrt (Real.tanh 1)) ^ 2 := by
  have hT : 0 < Real.tanh 1 := (by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _))
  have hkin : Real.sqrt (Real.tanh 1) * Real.tanh 1 =
      1 * Real.tanh (1 * 1) * Real.sqrt (Real.tanh 1) := by
    rw [mul_one, one_mul, mul_comm]
  have hdyn : Real.sqrt (Real.tanh 1) * Real.sqrt (Real.tanh 1) = 1 * Real.tanh 1 := by
    rw [one_mul]
    exact Real.mul_self_sqrt hT.le
  exact EarthScience.dispersion_positive (Real.sqrt (Real.tanh 1)) 1 1 1
    (Real.tanh 1) (Real.sqrt (Real.tanh 1)) (by norm_num) (by norm_num) (by norm_num)
    hT.ne' hkin hdyn

/-- Range check: the finite-depth factor `tanh (k H)` at `k H = 5` lies in
`(0, 1)`, as it does for every positive argument. -/
example : 0 < Real.tanh 5 ∧ Real.tanh 5 < 1 :=
  ⟨(by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _)), Real.tanh_lt_one 5⟩

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.O04ShallowWater

/-!
# Shallow-water waves, tides, and sea level

Concrete consumers of `PhyslibExt.EarthScience.O04ShallowWater`.

## i. Overview

Wave speed for `g = 9.8`, `H = 10`, and the zero-field instance of the wave equation.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.O04ShallowWater`
-/

/-- Wave speed for `g = 9.8`, `H = 10`: `√98 > 0` and `(√98)² = 98`. -/
example : 0 < Real.sqrt ((9.8 : ℝ) * 10) ∧ Real.sqrt ((9.8 : ℝ) * 10) ^ 2 = (9.8 : ℝ) * 10 :=
  EarthScience.shallow_water_wave_speed (by norm_num) (by norm_num)

/-- Zero-field instance of the wave equation: `η = u = 0` satisfies the system. -/
example : deriv (fun t' => deriv (fun s => (0 : ℝ → ℝ → ℝ) s (0 : ℝ)) t') (0 : ℝ) =
    (9.8 : ℝ) * 10 * deriv (fun x' => deriv (fun x'' => (0 : ℝ → ℝ → ℝ) (0 : ℝ) x'') x') (0 : ℝ) :=
      by
  have h : ∀ (t x : ℝ), HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-(10 : ℝ) * deriv (fun _ : ℝ => (0 : ℝ))
    x) t := by
    intro t x
    simpa using (hasDerivAt_const t (0 : ℝ))
  exact EarthScience.shallow_water_wave_eq (η := fun _ _ => 0) (u := fun _ _ => 0) (H := 10) (g :=
    9.8) 0 0
    (by intro t x; simpa using (hasDerivAt_const t (0 : ℝ)))
    (by intro t x; simpa using (hasDerivAt_const t (0 : ℝ)))
    (by intro t x; simpa using (hasDerivAt_const t (0 : ℝ)))
    (by intro t x; simp)

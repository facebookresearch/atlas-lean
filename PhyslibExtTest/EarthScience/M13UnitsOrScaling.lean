/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.M13UnitsOrScaling

/-!
# Advection-diffusion scaling checks

Concrete consumers of `PhyslibExt.EarthScience.M13UnitsOrScaling`:
a numeric nondimensionalization, the Péclet reciprocal identity,
and the degenerate `chatxx = 0` case (then `ĉ_t̂ + ĉ_x̂ = 0`).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric nondimensionalization
- B. Péclet identity
- C. Degenerate second derivative

## iv. References

- `PhyslibExt.EarthScience.M13UnitsOrScaling`
-/

/-- Numeric nondimensionalization: `L = 2, U = 3, D = 1, C0 = 5`,
scaled values `1, 2, 18`, dimensional values `7.5, 5, 22.5`. -/
example : (1 : ℝ) + 2 = (1 / (3 * 2 / 1)) * 18 :=
  EarthScience.advection_diffusion_nondimensional
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 5)
    (by norm_num : (7.5 : ℝ) = 5 * (3 / 2) * 1)
    (by norm_num : (5 : ℝ) = (5 / 2) * 2)
    (by norm_num : (22.5 : ℝ) = (5 / 2 ^ 2) * 18)
    (by norm_num : (7.5 : ℝ) + 3 * 5 = 1 * 22.5)

/-- Péclet reciprocal at `L = 2, U = 3, D = 1`: `1 / 6 = 1 / 6`. -/
example : 0 < (3 : ℝ) * 2 / 1 ∧ 1 / ((3 : ℝ) * 2 / 1) = 1 / (3 * 2) :=
  EarthScience.peclet_pos (by norm_num) (by norm_num) (by norm_num)

/-- Degenerate `ĉ_x̂x̂ = 0`: the scaled equation forces
`ĉ_t̂ + ĉ_x̂ = 0`; here `ĉ_t̂ = 1, ĉ_x̂ = -1`. -/
example : (1 : ℝ) + (-1) = (1 / ((3 : ℝ) * 2 / 1)) * 0 :=
  EarthScience.advection_diffusion_nondimensional
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 5)
    (by norm_num : (7.5 : ℝ) = 5 * (3 / 2) * 1)
    (by norm_num : (-2.5 : ℝ) = (5 / 2) * (-1))
    (by norm_num : (0 : ℝ) = (5 / 2 ^ 2) * 0)
    (by norm_num : (7.5 : ℝ) + 3 * (-2.5) = 1 * 0)

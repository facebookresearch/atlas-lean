 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.A06DropletGrowth

/-!
# Diffusion-limited droplet growth checks

Concrete consumers of `PhyslibExt.EarthScience.A06DropletGrowth`:
`r0 = 3, K = 2, S = 1, t = 4` (`r = 5`, `r^2 = 25`, `r' = 2/5`),
no supersaturation, and evaporation `S = -1` at `t = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.A06DropletGrowth`
-/

/-- Numeric radius squared: `r0 = 3, K = 2, S = 1, t = 4` gives `r^2 = 25`. -/
example : (Real.sqrt ((3:ℝ) ^ 2 + 2 * 2 * 1 * 4)) ^ 2 = 25 := by
  have h := EarthScience.a06_radius_sq (r0 := 3) (K := 2) (S := 1) (t := 4)
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

/-- Numeric radius: `sqrt(25) = 5`. -/
example : Real.sqrt ((3:ℝ) ^ 2 + 2 * 2 * 1 * 4) = 5 := by
  rw [show ((3:ℝ) ^ 2 + 2 * 2 * 1 * 4) = (5:ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Numeric squared-radius derivative: `(r^2)' = 4` at the numeric point. -/
example :
    HasDerivAt (fun t => (Real.sqrt ((3:ℝ) ^ 2 + 2 * 2 * 1 * t)) ^ 2) (2 * 2 * 1) 4 :=
  EarthScience.a06_radius_sq_hasDerivAt (r0 := 3) (K := 2) (S := 1) (by norm_num) (by norm_num) 4 (by norm_num)

/-- Numeric radius derivative: `r'(4) = 2/5`. -/
example :
    HasDerivAt (fun t => Real.sqrt ((3:ℝ) ^ 2 + 2 * 2 * 1 * t))
      (2 * 1 / Real.sqrt ((3:ℝ) ^ 2 + 2 * 2 * 1 * 4)) 4 :=
  EarthScience.a06_radius_hasDerivAt (r0 := 3) (K := 2) (S := 1) (by norm_num) (by norm_num) 4 (by rw [show ((3:ℝ) ^ 2 + 2 * 2 * 1 * 4) = (5:ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]; norm_num)

/-- No supersaturation: `S = 0` keeps `r = 3`. -/
example : Real.sqrt ((3:ℝ) ^ 2 + 2 * 2 * (0:ℝ) * 5) = 3 :=
  EarthScience.a06_no_supersaturation (r0 := 3) (K := 2) (t := 5) (by norm_num) (by norm_num)


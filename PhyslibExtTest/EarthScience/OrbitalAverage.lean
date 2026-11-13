/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.OrbitalAverage

/-!
# Paleoclimate proxies and orbital forcing

Concrete consumers of `PhyslibExt.EarthScience.OrbitalAverage`.

## i. Overview

Circular case `e = 0`, `a = 1`, `h = 1`: the average of `1 / r²` is `1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.OrbitalAverage`
-/

/-- Circular case `e = 0`: `r = 1`, average is `1 / (1 * √1) = 1`. -/
example : (∫ θ in (0)..(2 * Real.pi), (1 / (1 : ℝ → ℝ) θ ^ 2) * (((1 : ℝ → ℝ) θ) ^ 2 / 1)) /
    (∫ θ in (0)..(2 * Real.pi), ((1 : ℝ → ℝ) θ) ^ 2 / 1) =
    1 / ((1 : ℝ) ^ 2 * Real.sqrt (1 - (0 : ℝ) ^ 2)) := by
  have hArea : ∫ θ in (0)..(2 * Real.pi), ((fun _ => (1 : ℝ)) θ) ^ 2 =
      2 * Real.pi * (1 : ℝ) ^ 2 * Real.sqrt (1 - (0 : ℝ) ^ 2) := by
    simp [intervalIntegral.integral_const]
  exact EarthScience.orbital_time_average_inv_r_sq (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => 1) (by intro θ; simp) hArea

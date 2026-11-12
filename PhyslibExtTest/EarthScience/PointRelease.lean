/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.PointRelease

/-!
# Point-release kernel checks

Concrete consumers of `PhyslibExt.EarthScience.PointRelease`: the
Gaussian kernel with `M = D = 1`, `U = k = 0`, `t = 1` (a nonzero
Gaussian), its inventory, and the degenerate zero-mass case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`M = D = 1`, `U = k = 0`, `t = 1`, the kernel is
`exp (-x² / 4) / √(4π)` and its inventory is `1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. The unit Gaussian kernel
- B. Inventory and zero mass

## iv. References

- `PhyslibExt.EarthScience.PointRelease`
-/

/-- The unit Gaussian kernel solves the heat equation at `t = 1`, `x = 0`,
as an instance of the advection-diffusion-decay theorem with `U = k = 0`. -/
example :
    deriv (fun t => 1 * Real.exp (-0 * t) * Real.exp (-(0 - 0 * t) ^ 2 / (4 * 1 * t)) /
        Real.sqrt (4 * Real.pi * 1 * t)) 1 +
      0 * deriv (fun x => 1 * Real.exp (-0 * 1) * Real.exp (-(x - 0 * 1) ^ 2 / (4 * 1 * 1)) /
        Real.sqrt (4 * Real.pi * 1 * 1)) 0 =
      1 * deriv (fun x => deriv (fun x' => 1 * Real.exp (-0 * 1) *
        Real.exp (-(x' - 0 * 1) ^ 2 / (4 * 1 * 1)) /
        Real.sqrt (4 * Real.pi * 1 * 1)) x) 0 -
      0 * (1 * Real.exp (-0 * 1) * Real.exp (-(0 - 0 * 1) ^ 2 / (4 * 1 * 1)) /
        Real.sqrt (4 * Real.pi * 1 * 1)) :=
  EarthScience.point_release_solves_adr 1 1 0 0 1 0 (by norm_num) (by norm_num)

/-- The unit Gaussian kernel is nonzero at its peak: `c(1, 0) > 0`. -/
example : 0 < 1 * Real.exp (-0 * 1) * Real.exp (-(0 - 0 * 1) ^ 2 / (4 * 1 * 1)) /
    Real.sqrt (4 * Real.pi * 1 * 1) := by
  positivity

/-- Inventory of the unit Gaussian kernel is `1`. -/
example : (∫ x : ℝ, 1 * Real.exp (-0 * 1) * Real.exp (-(x - 0 * 1) ^ 2 / (4 * 1 * 1)) /
    Real.sqrt (4 * Real.pi * 1 * 1)) = 1 := by
  have h := EarthScience.point_release_integral 1 1 0 0 1 (by norm_num) (by norm_num)
  simpa using h

/-- Zero mass: the kernel is identically zero and its inventory is zero. -/
example (D k U t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    (∫ x : ℝ, 0 * Real.exp (-k * t) * Real.exp (-(x - U * t) ^ 2 / (4 * D * t)) /
      Real.sqrt (4 * Real.pi * D * t)) = 0 := by
  have h := EarthScience.point_release_integral 0 D k U t hD ht
  rw [zero_mul] at h
  convert h using 2
  funext x
  simp

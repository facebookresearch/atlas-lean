/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.RossbyDispersion

/-!
# Beta-plane Rossby mode checks

Concrete consumers of `PhyslibExt.EarthScience.RossbyDispersion`.

## i. Overview

Concrete mode `A = 1`, `β = 0.5`, `k = 2`, `l = 1`,
`ω = -0.2 = -β k / (k² + l²)`: the dispersion factor
`(k² + l²) ω + β k` vanishes, and the mode satisfies its dispersion
relation. Boundary cases, both through the public residual theorem
`EarthScience.rossby_mode_beta_plane_residual` applied to the full
derivative residual: `A = 0` (zero mode, residual zero for every `β`,
`k`, `l` and `ω`), and `k = l = 0` (excluded from the dispersion
theorem by `k² + l² ≠ 0`; the mode is spatially uniform and the
residual vanishes for every `ω`).

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete and boundary checks

## iv. References

- `PhyslibExt.EarthScience.RossbyDispersion`
-/

/-- Concrete dispersion factor: `(2² + 1²) * (-0.2) + 0.5 * 2 = 0`. -/
example : ((2 : ℝ) ^ 2 + (1 : ℝ) ^ 2) * (-0.2) + 0.5 * 2 = 0 := by norm_num

/-- Concrete mode satisfies its dispersion relation. -/
example : deriv (fun τ => deriv (fun u => deriv (fun u' => (1 : ℝ) * Real.cos (2 * u' + 1 * (0 : ℝ) - (-0.5 * 2 / (2 ^ 2 + 1 ^ 2)) * τ)) u) (0 : ℝ) +
        deriv (fun v => deriv (fun v' => (1 : ℝ) * Real.cos (2 * (0 : ℝ) + 1 * v' - (-0.5 * 2 / (2 ^ 2 + 1 ^ 2)) * τ)) v) (0 : ℝ)) (0 : ℝ) +
      0.5 * deriv (fun u => (1 : ℝ) * Real.cos (2 * u + 1 * (0 : ℝ) - (-0.5 * 2 / (2 ^ 2 + 1 ^ 2)) * (0 : ℝ))) (0 : ℝ) = 0 :=
  EarthScience.rossby_mode_satisfies_dispersion (A := (1 : ℝ)) (β := 0.5) (k := 2) (l := 1)
    (t := 0) (x := 0) (y := 0) (by norm_num)

/-- Boundary case `A = 0`: the full residual of the zero mode vanishes for every `β`, `k`, `l`
and `ω`. -/
example (β k l ω t x y : ℝ) :
    deriv (fun τ =>
        deriv (fun u => deriv (fun u' => (0 : ℝ) * Real.cos (k * u' + l * y - ω * τ)) u) x +
        deriv (fun v => deriv (fun v' => (0 : ℝ) * Real.cos (k * x + l * v' - ω * τ)) v) y) t +
      β * deriv (fun u => (0 : ℝ) * Real.cos (k * u + l * y - ω * t)) x = 0 :=
  EarthScience.rossby_mode_beta_plane_residual.trans (by ring)

/-- Boundary case `k = l = 0`: the mode `A cos(-ω t)` is spatially uniform, and its full residual
vanishes for every `A`, `β` and `ω`, although the dispersion theorem excludes `k² + l² = 0`. -/
example (A β ω t x y : ℝ) :
    deriv (fun τ => deriv (fun u => deriv (fun u' => A * Real.cos (0 * u' + 0 * y - ω * τ)) u) x +
        deriv (fun v => deriv (fun v' => A * Real.cos (0 * x + 0 * v' - ω * τ)) v) y) t +
      β * deriv (fun u => A * Real.cos (0 * u + 0 * y - ω * t)) x = 0 :=
  EarthScience.rossby_mode_beta_plane_residual.trans (by ring)

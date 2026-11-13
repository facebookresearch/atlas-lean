/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.EkmanSpiral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ekman spiral checks

Concrete consumers of `PhyslibExt.EarthScience.EkmanSpiral` with
`a = 1 / 2`, `nu = 2`, `f = 1` (so `2 * nu * a ^ 2 = f`): surface
values and shear, the profile a quarter-period down (`zeta = pi`, where
`a * zeta = pi / 2`), the ODE at `zeta = 0`, and decay at depth.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Surface, quarter-period, ODE, and decay checks

## iv. References

- `PhyslibExt.EarthScience.EkmanSpiral`
-/

/-- Surface value `u(0) = 1`. -/
example : EarthScience.ekmanSpiralU (1 / 2 : ℝ) 0 = 1 :=
  (EarthScience.ekman_spiral_boundary (1 / 2 : ℝ)).1

/-- Surface value `v(0) = 0`. -/
example : EarthScience.ekmanSpiralV (1 / 2 : ℝ) 0 = 0 :=
  (EarthScience.ekman_spiral_boundary (1 / 2 : ℝ)).2.1

/-- Surface shear `u'(0) = -1 / 2`. -/
example : EarthScience.ekmanSpiralUPrime (1 / 2 : ℝ) 0 = -(1 / 2 : ℝ) :=
  (EarthScience.ekman_spiral_boundary (1 / 2 : ℝ)).2.2.1

/-- Surface shear `v'(0) = 1 / 2`. -/
example : EarthScience.ekmanSpiralVPrime (1 / 2 : ℝ) 0 = (1 / 2 : ℝ) :=
  (EarthScience.ekman_spiral_boundary (1 / 2 : ℝ)).2.2.2

/-- A quarter-period down (`zeta = pi`, `a * zeta = pi / 2`), the
along-component vanishes: `u(pi) = 0`. -/
example : EarthScience.ekmanSpiralU (1 / 2 : ℝ) Real.pi = 0 := by
  have h : (1 / 2 : ℝ) * Real.pi = Real.pi / 2 := by ring
  show Real.exp (-(1 / 2 : ℝ) * Real.pi) * Real.cos ((1 / 2 : ℝ) * Real.pi) = 0
  rw [h, Real.cos_pi_div_two, mul_zero]

/-- At the same depth the cross-component is the pure envelope:
`v(pi) = exp(-pi / 2)`, nonzero (non-vacuous decay profile). -/
example : EarthScience.ekmanSpiralV (1 / 2 : ℝ) Real.pi =
    Real.exp (-Real.pi / 2) := by
  have h : (1 / 2 : ℝ) * Real.pi = Real.pi / 2 := by ring
  have h2 : -(1 / 2 : ℝ) * Real.pi = -Real.pi / 2 := by ring
  show Real.exp (-(1 / 2 : ℝ) * Real.pi) * Real.sin ((1 / 2 : ℝ) * Real.pi) =
    Real.exp (-Real.pi / 2)
  rw [h, h2, Real.sin_pi_div_two, mul_one]

/-- The ODE at `zeta = 0` for `a = 1 / 2`, `nu = 2`, `f = 1`:
`2 * u''(0) = v(0) = 0`. -/
example : (2 : ℝ) *
      deriv (fun ζ => deriv (EarthScience.ekmanSpiralU (1 / 2 : ℝ)) ζ) 0 =
    (1 : ℝ) * EarthScience.ekmanSpiralV (1 / 2 : ℝ) 0 :=
  (EarthScience.ekman_spiral_ode (1 / 2 : ℝ) 2 1 0 (by norm_num)).1

/-- Decay at depth for `a = 1 / 2`: both components tend to `0`. -/
example : Filter.Tendsto (EarthScience.ekmanSpiralU (1 / 2 : ℝ)) Filter.atTop
      (nhds 0) ∧
    Filter.Tendsto (EarthScience.ekmanSpiralV (1 / 2 : ℝ)) Filter.atTop
      (nhds 0) :=
  EarthScience.ekman_spiral_decay (1 / 2 : ℝ) (by norm_num)

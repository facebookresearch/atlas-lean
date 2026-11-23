/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.AngularMomentumCirculation

/-!
# Angular-momentum zonal wind checks

Concrete consumers of `PhyslibExt.EarthScience.AngularMomentumCirculation`: the
zonal wind at 30° latitude for unit `Ω` and `a`, the equator case, and the
degenerate zero-rotation case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At
`φ = π/6` with `Ω = a = 1`, the conserved parcel has
`u = sin²(π/6) / cos(π/6) = 1 / (2√3)`; the conservation hypothesis is
checked numerically from `sin(π/6) = 1/2` and `cos(π/6) = √3/2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Zonal wind at 30 degrees
- B. Equator and zero-rotation cases

## iv. References

- `PhyslibExt.EarthScience.AngularMomentumCirculation`
-/

/-- Zonal wind at 30 degrees for unit rotation and radius:
`u = 1 / (2√3)`. -/
example : (1 : ℝ) / (2 * Real.sqrt 3) =
    1 * 1 * (Real.sin (Real.pi / 6)) ^ 2 / Real.cos (Real.pi / 6) := by
  rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
  have hne : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

/-- The conservation hypothesis holds at 30 degrees for that wind value. -/
example : (1 * 1 * Real.cos (Real.pi / 6) + 1 / (2 * Real.sqrt 3)) *
    (1 * Real.cos (Real.pi / 6)) = 1 * 1 ^ 2 := by
  rw [Real.cos_pi_div_six]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  nlinarith [h3]

/-- The main theorem, applied at 30 degrees, gives the wind above. -/
example (hφ : |(Real.pi / 6 : ℝ)| < Real.pi / 2) :
    (1 : ℝ) / (2 * Real.sqrt 3) =
      1 * 1 * (Real.sin (Real.pi / 6)) ^ 2 / Real.cos (Real.pi / 6) := by
  have hcons : (1 * 1 * Real.cos (Real.pi / 6) + 1 / (2 * Real.sqrt 3)) *
      (1 * Real.cos (Real.pi / 6)) = 1 * 1 ^ 2 := by
    rw [Real.cos_pi_div_six]
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hne : Real.sqrt 3 ≠ 0 := by positivity
    field_simp
    nlinarith [h3]
  exact EarthScience.angular_momentum_zonal_wind 1 1 (Real.pi / 6)
    (1 / (2 * Real.sqrt 3)) (by norm_num) hφ hcons

/-- Equator case: with `Ω = 1`, `a = 2`, a parcel at rest stays at rest. -/
example : True := by
  have h : (0 : ℝ) = 0 :=
    EarthScience.angular_momentum_zonal_wind_equator 1 2 0 (by norm_num) (by norm_num)
  trivial

/-- Zero rotation: with `Ω = 0` the wind must vanish wherever conservation
holds. -/
example (a φ u : ℝ) (ha : 0 < a) (hφ : |φ| < Real.pi / 2)
    (hcons : (0 * a * Real.cos φ + u) * (a * Real.cos φ) = 0 * a ^ 2) :
    u = 0 := by
  have h := EarthScience.angular_momentum_zonal_wind 0 a φ u ha hφ hcons
  simpa using h

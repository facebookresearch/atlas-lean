/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.A04ThermalWind

/-!
# Thermal-wind checks

Concrete consumers of `PhyslibExt.EarthScience.A04ThermalWind`:
the public shapes of the three theorems, the thermal-wind relations
for linear profiles with `f = 1, rho0 = 1, g = 10, rho_y = 2, rho_x = 3`,
and the no-gradient boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`py z = -20 * z`, `px z = -30 * z`, `ug z = 20 * z`, `vg z = -30 * z`,
the shears are `A = 20`, `B = -30`, and
`f * A = (g / rho0) * rho_y = 20`, `f * B = -(g / rho0) * rho_x = -30`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Thermal-wind shapes
- B. Linear-profile case and no-gradient boundary

## iv. References

- `PhyslibExt.EarthScience.A04ThermalWind`
-/

/-- Public shape of the thermal-wind theorem. -/
example {f rho0 g rho_y rho_x : ℝ} {ug vg py px : ℝ → ℝ} {t : ℝ} {A B Dpy Dpx : ℝ}
    (hf : f ≠ 0) (hrho : rho0 ≠ 0)
    (hug : HasDerivAt ug A t) (hvg : HasDerivAt vg B t)
    (hpy : HasDerivAt py Dpy t) (hpx : HasDerivAt px Dpx t)
    (hgeo_u : ∀ z, f * ug z = -py z / rho0)
    (hgeo_v : ∀ z, f * vg z = px z / rho0)
    (hhydro_y : Dpy = -g * rho_y) (hhydro_x : Dpx = -g * rho_x) :
    f * A = (g / rho0) * rho_y ∧ f * B = -(g / rho0) * rho_x :=
  EarthScience.thermal_wind hf hrho hug hvg hpy hpx hgeo_u hgeo_v hhydro_y hhydro_x

/-- Linear-profile case: `f = 1, rho0 = 1, g = 10, rho_y = 2, rho_x = 3`. -/
example :
    (1 : ℝ) * (20 : ℝ) = (10 / 1) * 2 ∧ (1 : ℝ) * (-30 : ℝ) = -((10 / 1) * 3) := by
  norm_num

/-- Linear functions satisfy the geostrophic balances and derivative data. -/
example (t : ℝ) :
    (1 : ℝ) * (20 : ℝ) = (10 / 1) * 2 ∧ (1 : ℝ) * (-30 : ℝ) = (-(10 / 1)) * 3 := by
  have hug : HasDerivAt (fun z : ℝ => 20 * z) (20 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (20 : ℝ)
  have hvg : HasDerivAt (fun z : ℝ => -30 * z) (-30 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (-30 : ℝ)
  have hpy : HasDerivAt (fun z : ℝ => -20 * z) (-20 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (-20 : ℝ)
  have hpx : HasDerivAt (fun z : ℝ => -30 * z) (-30 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (-30 : ℝ)
  have hgeo_u : ∀ z, (1 : ℝ) * (20 * z) = -(-20 * z) / 1 := by
    intro z; ring
  have hgeo_v : ∀ z, (1 : ℝ) * (-30 * z) = (-30 * z) / 1 := by
    intro z; ring
  exact EarthScience.thermal_wind (f := 1) (rho0 := 1) (g := 10) (rho_y := 2)
    (rho_x := 3) (by norm_num) (by norm_num) hug hvg hpy hpx
    hgeo_u hgeo_v (by norm_num) (by norm_num)

/-- No-gradient boundary: `rho_y = rho_x = 0` gives zero shear products. -/
example {f rho0 g : ℝ} {ug vg py px : ℝ → ℝ} {t : ℝ} {A B Dpy Dpx : ℝ}
    (hf : f ≠ 0) (hrho : rho0 ≠ 0)
    (hug : HasDerivAt ug A t) (hvg : HasDerivAt vg B t)
    (hpy : HasDerivAt py Dpy t) (hpx : HasDerivAt px Dpx t)
    (hgeo_u : ∀ z, f * ug z = -py z / rho0)
    (hgeo_v : ∀ z, f * vg z = px z / rho0)
    (hhydro_y : Dpy = -g * 0) (hhydro_x : Dpx = -g * 0) :
    f * A = 0 ∧ f * B = 0 :=
  EarthScience.thermal_wind_no_gradient hf hrho hug hvg hpy hpx hgeo_u hgeo_v
    hhydro_y hhydro_x

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Balanced atmospheric winds

Under hydrostatic and f-plane geostrophic balances with constant
`f, rho0`, differentiating the geostrophic balances in `z` and using
the horizontally differentiated hydrostatic relations
`d/dz py = -g * rho_y`, `d/dz px = -g * rho_x` (commuting mixed
derivatives for C2 `p`) gives the thermal-wind relations
`f * d/dz ug = (g / rho0) * rho_y` and
`f * d/dz vg = -(g / rho0) * rho_x` in the chosen Boussinesq model.
With no horizontal density gradient there is no thermal-wind shear,
and for `f, g, rho0 > 0` a positive `rho_y` gives positive shear.
The atmospheric pressure-coordinate version requires a bridge, not a
rename; no such bridge is claimed here.

## i. Overview

Differentiate each geostrophic balance: the left side gives `f` times
the shear, the right side gives the `z`-derivative of the pressure
gradient over `rho0`. Uniqueness of derivatives plus the hydrostatic
relations convert these into the thermal-wind formulas.

## ii. Key results

- `EarthScience.thermal_wind_zonal`: the zonal relation from zonal data alone.
- `EarthScience.thermal_wind`: thermal-wind relations for both components.
- `EarthScience.thermal_wind_no_gradient`: no gradient, no shear.
- `EarthScience.thermal_wind_shear_sign`: hemispheric shear sign.

## iii. Table of contents

- A. Thermal wind

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed.,
  Cambridge University Press (2017), Chapter 2, section on geostrophic and
  thermal wind balance (Boussinesq form). Conventions there and here:
  Cartesian f-plane with `x` east, `y` north, `z` up, Coriolis parameter
  `f` (positive in the Northern Hemisphere), constant reference density
  `rho0`. Geostrophic balance `f k × u_g = -∇p / rho0` is, componentwise,
  `f * ug = -py / rho0` and `f * vg = px / rho0` (`hgeo_u`, `hgeo_v`, with
  `py = ∂p/∂y`, `px = ∂p/∂x`); hydrostatic balance `∂p/∂z = -rho * g`,
  differentiated in `y` and `x` with mixed partials commuted, gives
  `hhydro_y`, `hhydro_x`. The conclusions of `thermal_wind` are the
  Boussinesq thermal-wind balance `f ∂u_g/∂z = k × ∇b` for the buoyancy
  `b = -g * rho / rho0` (up to an additive constant), i.e.
  `f * ∂ug/∂z = (g / rho0) * rho_y` and `f * ∂vg/∂z = -(g / rho0) * rho_x`.
- `HasDerivAt.const_mul` / `HasDerivAt.div_const` / `HasDerivAt.unique` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Zonal thermal wind, one component: differentiating the zonal geostrophic
balance `f * ug = -py / rho0` in `z` and using the hydrostatic relation
differentiated in `y`, `d/dz py = -g * rho_y`, gives
`f * d/dz ug = (g / rho0) * rho_y`. Here `A` is the `z`-derivative of `ug`
and `Dpy` that of `py` at `t`; no meridional data is needed. -/
lemma thermal_wind_zonal {f rho0 g rho_y : ℝ} {ug py : ℝ → ℝ} {t A Dpy : ℝ}
    (hrho : rho0 ≠ 0) (hug : HasDerivAt ug A t) (hpy : HasDerivAt py Dpy t)
    (hgeo_u : ∀ z, f * ug z = -py z / rho0) (hhydro_y : Dpy = -g * rho_y) :
    f * A = (g / rho0) * rho_y := by
  have hLHSu : HasDerivAt (fun z => f * ug z) (f * A) t :=
    HasDerivAt.const_mul f hug
  have hRHSu : HasDerivAt (fun z => -py z / rho0) (-Dpy / rho0) t :=
    HasDerivAt.div_const hpy.neg rho0
  have heq_u : (fun z => f * ug z) = (fun z => -py z / rho0) := funext hgeo_u
  rw [heq_u] at hLHSu
  rw [hLHSu.unique hRHSu, hhydro_y]
  field_simp

set_option linter.unusedVariables false in
/-- Thermal wind: differentiating the f-plane geostrophic balances
`f * ug = -py / rho0`, `f * vg = px / rho0` in `z`, and using the
hydrostatic relations differentiated in the horizontal,
`d/dz py = -g * rho_y`, `d/dz px = -g * rho_x` (commuting mixed
derivatives), gives `f * d/dz ug = (g / rho0) * rho_y` and
`f * d/dz vg = -(g / rho0) * rho_x`. Here `A, B` are the `z`-derivatives
of `ug, vg` and `Dpy, Dpx` the `z`-derivatives of `py, px` at `t`. -/
theorem thermal_wind {f rho0 g rho_y rho_x : ℝ} {ug vg py px : ℝ → ℝ} {t : ℝ}
    {A B Dpy Dpx : ℝ}
    (hf : f ≠ 0) (hrho : rho0 ≠ 0)
    (hug : HasDerivAt ug A t) (hvg : HasDerivAt vg B t)
    (hpy : HasDerivAt py Dpy t) (hpx : HasDerivAt px Dpx t)
    (hgeo_u : ∀ z, f * ug z = -py z / rho0)
    (hgeo_v : ∀ z, f * vg z = px z / rho0)
    (hhydro_y : Dpy = -g * rho_y) (hhydro_x : Dpx = -g * rho_x) :
    f * A = (g / rho0) * rho_y ∧ f * B = -(g / rho0) * rho_x := by
  have hA : f * A = (g / rho0) * rho_y := thermal_wind_zonal hrho hug hpy hgeo_u hhydro_y
  have hLHSv : HasDerivAt (fun z => f * vg z) (f * B) t :=
    HasDerivAt.const_mul f hvg
  have hRHSv : HasDerivAt (fun z => px z / rho0) (Dpx / rho0) t :=
    HasDerivAt.div_const hpx rho0
  have heq_v : (fun z => f * vg z) = (fun z => px z / rho0) := funext hgeo_v
  rw [heq_v] at hLHSv
  have hB_eq : f * B = Dpx / rho0 := hLHSv.unique hRHSv
  have hB : f * B = -(g / rho0) * rho_x := by
    rw [hB_eq, hhydro_x]
    field_simp
  exact ⟨hA, hB⟩

/-- No horizontal density gradient: `rho_y = rho_x = 0` gives no thermal
wind shear, `A = 0` and `B = 0` (cancelling `f ≠ 0`). -/
theorem thermal_wind_no_gradient {f rho0 g : ℝ} {ug vg py px : ℝ → ℝ} {t : ℝ}
    {A B Dpy Dpx : ℝ}
    (hf : f ≠ 0) (hrho : rho0 ≠ 0)
    (hug : HasDerivAt ug A t) (hvg : HasDerivAt vg B t)
    (hpy : HasDerivAt py Dpy t) (hpx : HasDerivAt px Dpx t)
    (hgeo_u : ∀ z, f * ug z = -py z / rho0)
    (hgeo_v : ∀ z, f * vg z = px z / rho0)
    (hhydro_y : Dpy = -g * 0) (hhydro_x : Dpx = -g * 0) :
    A = 0 ∧ B = 0 := by
  have h := thermal_wind hf hrho hug hvg hpy hpx hgeo_u hgeo_v hhydro_y hhydro_x
  simpa [hf] using h

/-- Hemispheric sign: for `f, g, rho0 > 0`, a positive northward density
gradient `rho_y > 0` gives positive vertical shear `A > 0`. Only the zonal
balance is needed (`thermal_wind_zonal`). -/
theorem thermal_wind_shear_sign {f rho0 g rho_y : ℝ} {ug py : ℝ → ℝ} {t A Dpy : ℝ}
    (hf : 0 < f) (hrho : 0 < rho0) (hg : 0 < g) (hry : 0 < rho_y)
    (hug : HasDerivAt ug A t) (hpy : HasDerivAt py Dpy t)
    (hgeo_u : ∀ z, f * ug z = -py z / rho0) (hhydro_y : Dpy = -g * rho_y) :
    0 < A := by
  have h1 := thermal_wind_zonal (ne_of_gt hrho) hug hpy hgeo_u hhydro_y
  have hpos : 0 < (g / rho0) * rho_y := by positivity
  have hmul : 0 < f * A := by
    rw [h1]
    exact hpos
  exact (mul_pos_iff_of_pos_left hf).mp hmul

end EarthScience

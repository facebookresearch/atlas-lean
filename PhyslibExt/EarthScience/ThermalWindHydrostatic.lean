/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import PhyslibExt.EarthScience.Geostrophic
import PhyslibExt.EarthScience.ThermalWind

/-!
# Thermal wind from hydrostatic balance of a pressure field

Hydrostatic balance of a `C²` pressure field and geostrophic balance give thermal wind balance,
with the mixed partial derivatives of the pressure commuted by a theorem rather than assumed.

## i. Overview

`EarthScience.thermal_wind` works on the vertical line through a point and takes as hypotheses
the hydrostatic relations already differentiated in the horizontal, `∂/∂z (∂p/∂y) = -g ∂ρ/∂y`
and `∂/∂z (∂p/∂x) = -g ∂ρ/∂x`; getting them from `∂p/∂z = -ρ g` means commuting mixed partial
derivatives of `p`. Here the fields live on `Space 3` at a fixed time, with coordinates `x 0`,
`x 1`, `x 2` pointing east, north and up, and `∂[i]` is Physlib's partial derivative
`Space.deriv`. For a `C²` pressure `p` and a density `ρ` in hydrostatic balance `∂p/∂z = -ρ g`,
Physlib's `Space.deriv_commute` (Mathlib's symmetry of the second derivative of a `C²` function,
`ContDiffAt.isSymmSndFDerivAt`) gives `∂/∂z (∂p/∂xᵢ) = ∂/∂xᵢ (∂p/∂z) = -g ∂ρ/∂xᵢ`. Geostrophic
balance `f u = -(1/ρ₀) ∂p/∂y`, `f v = (1/ρ₀) ∂p/∂x` with `f ≠ 0` makes `u` and `v` multiples of
the `C¹` pressure gradient (`EarthScience.geostrophic_velocity`), so their restrictions to the
vertical line have the derivatives that `thermal_wind` takes. The result is
`f ∂u/∂z = (g/ρ₀) ∂ρ/∂y` and `f ∂v/∂z = -(g/ρ₀) ∂ρ/∂x` at every point. Both balances are
hypotheses of a reduced model; no dynamics is derived.

## ii. Key results

- `EarthScience.thermal_wind_of_hydrostatic`: thermal wind balance from hydrostatic balance of a
  `C²` pressure field and geostrophic balance on `Space 3`.

## iii. Table of contents

- A. Thermal wind from hydrostatic balance

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed., Cambridge University Press,
  2017, Section 2.8 (Geostrophic and Thermal Wind Balance).
- `Space.deriv_commute` in Physlib (mixed partial derivatives of a `C²` function commute).
-/

@[expose] public section

open Space

namespace EarthScience

/-!
## A. Thermal wind from hydrostatic balance
-/

/-- **Thermal wind balance** from hydrostatic balance of a pressure field (f-plane, Boussinesq).
On `Space 3` with coordinates east, north and up, let the `C²` pressure `p` and the density `ρ`
satisfy hydrostatic balance `∂p/∂z = -ρ g`, and let the velocity `(u, v)` satisfy geostrophic
balance `f u = -(1/ρ₀) ∂p/∂y`, `f v = (1/ρ₀) ∂p/∂x` with `f ≠ 0` and `ρ₀ ≠ 0`. Then
`f ∂u/∂z = (g/ρ₀) ∂ρ/∂y` and `f ∂v/∂z = -(g/ρ₀) ∂ρ/∂x`: the horizontal density gradient
determines the vertical shear of the geostrophic wind. Unlike `thermal_wind`, the commuted
mixed partial derivatives of `p` are derived from `C²` regularity, not assumed. -/
theorem thermal_wind_of_hydrostatic {f g ρ₀ : ℝ} {p ρ u v : Space 3 → ℝ} (hf : f ≠ 0)
    (hρ₀ : ρ₀ ≠ 0) (hp : ContDiff ℝ 2 p) (hhydro : ∀ x, ∂[2] p x = -ρ x * g)
    (hu : ∀ x, f * u x = -∂[1] p x / ρ₀) (hv : ∀ x, f * v x = ∂[0] p x / ρ₀) (x : Space 3) :
    f * ∂[2] u x = g / ρ₀ * ∂[1] ρ x ∧ f * ∂[2] v x = -(g / ρ₀) * ∂[0] ρ x := by
  -- On the vertical line through `x`, a field differentiable at `x` has derivative `∂[2]`.
  have hline {F : Space 3 → ℝ} (hF : DifferentiableAt ℝ F x) :
      HasDerivAt (fun z : ℝ => F (x + z • Space.basis 2)) (∂[2] F x) 0 := by
    have hγ : HasDerivAt (fun z : ℝ => x + z • Space.basis 2) (Space.basis 2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Space.basis 2)).const_add x
    have hF' : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • Space.basis 2) := by
      rw [zero_smul, add_zero]
      exact hF.hasFDerivAt
    exact hF'.comp_hasDerivAt (0 : ℝ) hγ
  -- Geostrophic balance makes `u` and `v` multiples of the `C¹` pressure gradient.
  have hpd := Space.deriv_differentiable hp
  have hvel (y : Space 3) := geostrophic_velocity (px := ∂[0] p y) (uy := v y) hf hρ₀ (hu y)
    (by linear_combination -hv y)
  have hud : DifferentiableAt ℝ u x := by
    rw [show u = fun y => -∂[1] p y / (ρ₀ * f) from funext fun y => (hvel y).1]
    fun_prop
  have hvd : DifferentiableAt ℝ v x := by
    rw [show v = fun y => ∂[0] p y / (ρ₀ * f) from funext fun y => (hvel y).2]
    fun_prop
  -- Commute the mixed partial derivatives of `p`, then use hydrostatic balance.
  have hmix (i : Fin 3) : ∂[2] (∂[i] p) x = -g * ∂[i] ρ x := by
    rw [Space.deriv_commute p hp,
      show ∂[2] p = (-g) • ρ from funext fun y => by simp [hhydro y, mul_comm]]
    change fderiv ℝ ((-g) • ρ) x (Space.basis i) = -g * fderiv ℝ ρ x (Space.basis i)
    rw [fderiv_const_smul_field]
    rfl
  exact thermal_wind hf hρ₀ (hline hud) (hline hvd) (hline (hpd 1 x)) (hline (hpd 0 x))
    (fun _ => hu _) (fun _ => hv _) (hmix 1) (hmix 0)

end EarthScience

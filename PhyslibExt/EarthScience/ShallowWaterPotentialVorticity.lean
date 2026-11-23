/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

/-!
# Shallow-water potential vorticity

Along a parcel trajectory, the potential vorticity `q = (ζ + f) / h`
with relative vorticity `ζ`, constant Coriolis parameter `f` and depth
`h` is conserved when the depth satisfies the continuity equation
`h' = -h D` and the absolute vorticity satisfies the vorticity equation
`(ζ + f)' = -(ζ + f) D`, with the same divergence `D` along the
trajectory. The quotient rule gives `q' = 0`: the two `D` terms cancel.

Conventions, following Vallis (see References): `'` is the derivative
along the parcel (the material derivative `D/Dt` of the source), `h` is the
depth of the fluid layer,
and `D = ∂u/∂x + ∂v/∂y` is the horizontal divergence of the velocity at the
parcel. The hypotheses are the shallow-water mass continuity equation
`Dh/Dt + h ∇·u = 0` and the absolute-vorticity equation
`D(ζ + f)/Dt + (ζ + f) ∇·u = 0`, read along one trajectory. The statements
take `f` constant, the f-plane case.

## i. Overview

`q' = ((ζ + f)' h - (ζ + f) h') / h²
= (-(ζ + f) D h + (ζ + f) h D) / h² = 0`, for `h ≠ 0`. Vanishing
derivative everywhere then gives `q(s) = q(t)` for all `s, t`.

## ii. Key results

- `EarthScience.shallow_water_potential_vorticity_hasDerivAt_zero`:
  `q` has zero derivative at a time `t` where `h t ≠ 0` and the continuity
  and vorticity equations hold (hypotheses at `t` only).
- `EarthScience.shallow_water_potential_vorticity_conserved`: `q` is
  conserved along the trajectory.

## iii. Table of contents

- A. Potential-vorticity conservation

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics: Fundamentals and
  Large-Scale Circulation*, 2nd ed., Cambridge University Press (2017),
  Chapter 3 (Shallow Water Systems and Isentropic Coordinates): the
  shallow-water mass continuity and vorticity equations and the material
  conservation of the shallow-water potential vorticity `(ζ + f) / h`.
- `HasDerivAt.fun_div`, `is_const_of_deriv_eq_zero` in Mathlib.

## A. Potential-vorticity conservation
-/

@[expose] public section

namespace EarthScience

/-- Potential vorticity along a parcel trajectory: if at time `t` the depth
is nonzero and satisfies `h' = -h D` (continuity with divergence `D`), and the
absolute vorticity satisfies `(ζ + f)' = -(ζ + f) D` (vorticity equation),
then the potential vorticity `q = (ζ + f) / h` has zero derivative at `t`.
Here `f` is the constant Coriolis parameter and `D` is the divergence along
the trajectory; the hypotheses are needed at `t` only. -/
theorem shallow_water_potential_vorticity_hasDerivAt_zero {f : ℝ} {ζ h D : ℝ → ℝ} {t : ℝ}
    (hh : h t ≠ 0)
    (hh' : HasDerivAt h (-(h t * D t)) t)
    (hζ : HasDerivAt (fun τ => ζ τ + f) (-((ζ t + f) * D t)) t) :
    HasDerivAt (fun τ => (ζ τ + f) / h τ) 0 t := by
  have hq := hζ.fun_div hh' hh
  have hnum : -((ζ t + f) * D t) * h t - (ζ t + f) * (-(h t * D t)) = 0 := by ring
  have hval : (-((ζ t + f) * D t) * h t - (ζ t + f) * (-(h t * D t))) / h t ^ 2 = 0 := by
    rw [hnum, zero_div]
  convert hq using 1
  exact hval.symm

/-- Potential vorticity is conserved along a parcel trajectory under the
shallow-water continuity and vorticity hypotheses above. -/
theorem shallow_water_potential_vorticity_conserved {f : ℝ} {ζ h D : ℝ → ℝ}
    (hh : ∀ t, h t ≠ 0)
    (hh' : ∀ t, HasDerivAt h (-(h t * D t)) t)
    (hζ : ∀ t, HasDerivAt (fun τ => ζ τ + f) (-((ζ t + f) * D t)) t)
    {s t : ℝ} :
    (ζ s + f) / h s = (ζ t + f) / h t := by
  have hq : ∀ t, HasDerivAt (fun τ => (ζ τ + f) / h τ) 0 t :=
    fun x => shallow_water_potential_vorticity_hasDerivAt_zero (hh x) (hh' x) (hζ x)
  have hdiff : Differentiable ℝ (fun τ => (ζ τ + f) / h τ) :=
    fun x => (hq x).differentiableAt
  have hderiv : ∀ x, deriv (fun τ => (ζ τ + f) / h τ) x = 0 :=
    fun x => (hq x).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv s t

end EarthScience

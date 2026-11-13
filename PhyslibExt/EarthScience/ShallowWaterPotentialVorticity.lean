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

## i. Overview

`q' = ((ζ + f)' h - (ζ + f) h') / h²
= (-(ζ + f) D h + (ζ + f) h D) / h² = 0`, for `h ≠ 0`. Vanishing
derivative everywhere then gives `q(s) = q(t)` for all `s, t`.

## ii. Key results

- `EarthScience.shallow_water_potential_vorticity_hasDerivAt_zero`:
  `q` has zero derivative.
- `EarthScience.shallow_water_potential_vorticity_conserved`: `q` is
  conserved along the trajectory.

## iii. Table of contents

- A. Potential-vorticity conservation

## iv. References

- `HasDerivAt.fun_div`, `is_const_of_deriv_eq_zero` in Mathlib.

## A. Potential-vorticity conservation
-/

@[expose] public section

namespace EarthScience

/-- Potential vorticity along a parcel trajectory: if the depth satisfies
`h' = -h D` (continuity with divergence `D`) and the absolute vorticity
satisfies `(ζ + f)' = -(ζ + f) D` (vorticity equation), then the potential
vorticity `q = (ζ + f) / h` has zero derivative. Here `f` is the constant
Coriolis parameter and `D` is the divergence along the trajectory. -/
theorem shallow_water_potential_vorticity_hasDerivAt_zero {f : ℝ} {ζ h D : ℝ → ℝ}
    (hh : ∀ t, h t ≠ 0)
    (hh' : ∀ t, HasDerivAt h (-(h t * D t)) t)
    (hζ : ∀ t, HasDerivAt (fun τ => ζ τ + f) (-((ζ t + f) * D t)) t)
    (t : ℝ) :
    HasDerivAt (fun τ => (ζ τ + f) / h τ) 0 t := by
  have hq := (hζ t).fun_div (hh' t) (hh t)
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
    fun t => shallow_water_potential_vorticity_hasDerivAt_zero hh hh' hζ t
  have hdiff : Differentiable ℝ (fun τ => (ζ τ + f) / h τ) :=
    fun x => (hq x).differentiableAt
  have hderiv : ∀ x, deriv (fun τ => (ζ τ + f) / h τ) x = 0 :=
    fun x => (hq x).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv s t

end EarthScience

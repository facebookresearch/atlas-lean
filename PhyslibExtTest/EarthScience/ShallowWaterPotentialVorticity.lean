/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ShallowWaterPotentialVorticity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Shallow-water potential vorticity checks

Concrete consumers of
`PhyslibExt.EarthScience.ShallowWaterPotentialVorticity`.

## i. Overview

Concrete parcel with constant divergence `D = 0.3`, depth
`h(t) = exp(-0.3 t)` and absolute vorticity `ζ(t) + f = 2 exp(-0.3 t)`
(`f = 1`, so `ζ(t) = 2 exp(-0.3 t) - 1`): the potential vorticity is
identically `2`. Boundary case `D = 0`: constant depth `h = 2` and constant
absolute vorticity `ζ + f = 3` satisfy the hypotheses of the conservation
theorem. Pointwise use: `h(τ) = τ` vanishes at `0`, so the global
hypotheses fail, but the pointwise derivative theorem applies at `t = 1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete and boundary checks

## iv. References

- `PhyslibExt.EarthScience.ShallowWaterPotentialVorticity`
-/

/-- Depth hypothesis for `h(t) = exp(-0.3 t)`, `D = 0.3`. -/
example : ∀ t, HasDerivAt (fun τ => Real.exp (-0.3 * τ))
    (-(Real.exp (-0.3 * t) * (0.3 : ℝ))) t := by
  intro t
  have hlin : HasDerivAt (fun τ : ℝ => -0.3 * τ) (-0.3) t := by
    simpa using (hasDerivAt_id' t).const_mul (-0.3 : ℝ)
  have h := hlin.exp
  have hval : Real.exp (-0.3 * t) * (-0.3) = -(Real.exp (-0.3 * t) * (0.3 : ℝ)) := by ring
  rwa [hval] at h

/-- Vorticity hypothesis for `ζ(t) + f = 2 exp(-0.3 t)`, `D = 0.3`. -/
example : ∀ t, HasDerivAt (fun τ => 2 * Real.exp (-0.3 * τ) - 1 + 1)
    (-(((2 * Real.exp (-0.3 * t) - 1 + 1)) * (0.3 : ℝ))) t := by
  intro t
  have hlin : HasDerivAt (fun τ : ℝ => -0.3 * τ) (-0.3) t := by
    simpa using (hasDerivAt_id' t).const_mul (-0.3 : ℝ)
  have h1 := hlin.exp
  have h2 := h1.const_mul (2 : ℝ)
  have hval : (2 : ℝ) * (Real.exp (-0.3 * t) * (-0.3)) =
      -((2 * Real.exp (-0.3 * t) - 1 + 1) * (0.3 : ℝ)) := by ring
  have h3 : HasDerivAt (fun τ => 2 * Real.exp (-0.3 * τ) - 1 + 1)
      (2 * (Real.exp (-0.3 * t) * (-0.3))) t := by
    simpa using h2
  rwa [hval] at h3

/-- Concrete conservation: `q(t) = 2` for all `t`, so `q(0) = q(1) = 2`. -/
example : ((2 * Real.exp (-0.3 * (0 : ℝ)) - 1 + 1) / Real.exp (-0.3 * (0 : ℝ))) =
    ((2 * Real.exp (-0.3 * (1 : ℝ)) - 1 + 1) / Real.exp (-0.3 * (1 : ℝ))) := by
  have hh : ∀ t, Real.exp (-0.3 * t) ≠ 0 := fun t => Real.exp_ne_zero _
  have hh' : ∀ t, HasDerivAt (fun τ => Real.exp (-0.3 * τ))
      (-(Real.exp (-0.3 * t) * (0.3 : ℝ))) t := by
    intro t
    have hlin : HasDerivAt (fun τ : ℝ => -0.3 * τ) (-0.3) t := by
      simpa using (hasDerivAt_id' t).const_mul (-0.3 : ℝ)
    have h := hlin.exp
    have hval : Real.exp (-0.3 * t) * (-0.3) = -(Real.exp (-0.3 * t) * (0.3 : ℝ)) := by ring
    rwa [hval] at h
  have hζ : ∀ t, HasDerivAt (fun τ => 2 * Real.exp (-0.3 * τ) - 1 + 1)
      (-(((2 * Real.exp (-0.3 * t) - 1 + 1)) * (0.3 : ℝ))) t := by
    intro t
    have hlin : HasDerivAt (fun τ : ℝ => -0.3 * τ) (-0.3) t := by
      simpa using (hasDerivAt_id' t).const_mul (-0.3 : ℝ)
    have h1 := hlin.exp
    have h2 := h1.const_mul (2 : ℝ)
    have hval : (2 : ℝ) * (Real.exp (-0.3 * t) * (-0.3)) =
        -((2 * Real.exp (-0.3 * t) - 1 + 1) * (0.3 : ℝ)) := by ring
    have h3 : HasDerivAt (fun τ => 2 * Real.exp (-0.3 * τ) - 1 + 1)
        (2 * (Real.exp (-0.3 * t) * (-0.3))) t := by
      simpa using h2
    rwa [hval] at h3
  exact EarthScience.shallow_water_potential_vorticity_conserved (f := (1 : ℝ))
    (ζ := fun τ => 2 * Real.exp (-0.3 * τ) - 1) (h := fun τ => Real.exp (-0.3 * τ))
    (D := fun _ => (0.3 : ℝ)) hh hh' hζ (s := (0 : ℝ)) (t := (1 : ℝ))

/-- Boundary case `D = 0`: constant depth `h = 2` and constant absolute
vorticity `ζ + f = 3` (`ζ = 2`, `f = 1`) satisfy the hypotheses of
`shallow_water_potential_vorticity_conserved`, which gives `q(0) = q(1)`,
here `q = 3 / 2`. -/
example : ((2 : ℝ) + 1) / 2 = ((2 : ℝ) + 1) / 2 :=
  EarthScience.shallow_water_potential_vorticity_conserved (f := (1 : ℝ))
    (ζ := fun _ => 2) (h := fun _ => 2) (D := fun _ => 0)
    (fun _ => two_ne_zero) (fun t => by simpa using hasDerivAt_const t (2 : ℝ))
    (fun t => by simpa using hasDerivAt_const t ((2 : ℝ) + 1)) (s := 0) (t := 1)

/-- Pointwise use: `h(τ) = τ` vanishes at `0`, so the global hypotheses of
`shallow_water_potential_vorticity_conserved` fail, but at `t = 1` (with
`D = -1`, `ζ(τ) = τ`, `f = 0`) the hypotheses hold and `q = (ζ + f) / h` has
zero derivative. -/
example : HasDerivAt (fun τ : ℝ => (τ + 0) / τ) 0 1 :=
  EarthScience.shallow_water_potential_vorticity_hasDerivAt_zero (f := 0) (ζ := fun τ => τ)
    (h := fun τ => τ) (D := fun _ => -1) one_ne_zero
    (by simpa using hasDerivAt_id' (1 : ℝ)) (by simpa using hasDerivAt_id' (1 : ℝ))

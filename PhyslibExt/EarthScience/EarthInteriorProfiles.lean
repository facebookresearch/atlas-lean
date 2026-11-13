/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Earth-interior profiles and elastic-density relations

## i. Overview

For the spherical enclosed-mass model `m' = 4 * π * r ^ 2 * ρ`,
gravity `g = G * m / r ^ 2`, and hydrostatic equilibrium
`p' = -ρ * g`, adding the radial/adiabatic homogeneous-composition
constitutive relation `dp / dr = φ * dρ / dr` gives
`dρ / dr = -ρ * g / φ`, where `φ` is the seismic bulk parameter
(`L ^ 2 / T ^ 2`) and `r` is the radial outward coordinate. In the
algebraic clauses below, `dp` means `dp / dr` and `drho` means
`dρ / dr`, both plain real numbers. Interfaces are treated separately;
no nonadiabatic claim is made, and the centre limit `r = 0` is
excluded from the gravity form.

## ii. Key results

- `EarthScience.density_gradient_adams_williamson`: the Adams-Williamson
  relation `dρ / dr = -ρ * g / φ`.
- `EarthScience.density_gradient_with_gravity`: the same relation with
  `g = G * m / r ^ 2` written out.
- `EarthScience.density_gradient_negative`: for positive `ρ, g, φ`,
  the density gradient is negative.
- `EarthScience.hasDerivAt_enclosed_mass_uniform`: uniform-density
  enclosed mass has derivative `4 * π * r ^ 2 * ρ` (shell relation).

## iii. Table of contents

- A. Adams-Williamson relation and sign
- B. Enclosed-mass derivative

## iv. References

- `HasDerivAt.const_mul`, `hasDerivAt_pow` in Mathlib.

## A. Adams-Williamson relation and sign
-/

@[expose] public section

namespace EarthScience

/-- Adams-Williamson relation: hydrostatic `dp = -ρ * g` together with the
constitutive relation `dp = φ * dρ` (φ the seismic parameter) gives
`dρ = -ρ * g / φ`, for `φ ≠ 0`. Here `dp` and `drho` are the radial
derivatives `dp / dr` and `dρ / dr`. -/
theorem density_gradient_adams_williamson {ρ g φ dp drho : ℝ} (hφ : φ ≠ 0)
    (h_hydro : dp = -ρ * g) (h_const : dp = φ * drho) :
    drho = -ρ * g / φ := by
  have h : φ * drho = -ρ * g := h_const.symm.trans h_hydro
  rw [eq_div_iff hφ]
  linarith

/-- The same relation with gravity written out as `g = G * m / r ^ 2`,
for `r > 0` (the `r = 0` centre limit is excluded). -/
theorem density_gradient_with_gravity {G m r ρ φ dp drho : ℝ} (_hr : 0 < r) (hφ : φ ≠ 0)
    (h_hydro : dp = -ρ * (G * m / r ^ 2)) (h_const : dp = φ * drho) :
    drho = -ρ * (G * m / r ^ 2) / φ := by
  have h : φ * drho = -ρ * (G * m / r ^ 2) := h_const.symm.trans h_hydro
  rw [eq_div_iff hφ]
  linarith

/-- For positive density, gravity and seismic parameter, the density
gradient is negative: density decreases outward. -/
theorem density_gradient_negative {ρ g φ drho : ℝ} (hρ : 0 < ρ) (hg : 0 < g)
    (hφ : 0 < φ) (h : drho = -ρ * g / φ) : drho < 0 := by
  rw [h]
  exact div_neg_of_neg_of_pos (by have h' := mul_pos hρ hg; linarith) hφ

/-! ## B. Enclosed-mass derivative -/

/-- Uniform-density enclosed mass `m(r) = (4 / 3) * π * r ^ 3 * ρ` has
derivative `m'(r) = 4 * π * r ^ 2 * ρ` (the spherical shell relation). -/
theorem hasDerivAt_enclosed_mass_uniform {ρ r : ℝ} :
    HasDerivAt (fun r => (4 / 3 : ℝ) * Real.pi * r ^ 3 * ρ)
      (4 * Real.pi * r ^ 2 * ρ) r := by
  have hfun : (fun r => (4 / 3 : ℝ) * Real.pi * r ^ 3 * ρ)
      = (fun r => ((4 / 3 : ℝ) * Real.pi * ρ) * r ^ 3) := by
    funext x
    ring
  rw [hfun]
  have h := HasDerivAt.const_mul ((4 / 3 : ℝ) * Real.pi * ρ) (hasDerivAt_pow 3 r)
  convert h using 1
  ring

end EarthScience

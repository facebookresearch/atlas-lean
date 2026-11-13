/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Ring

/-!
# Seawater state and stratification

For the incompressible Boussinesq profile `rho(z) = rho0 - beta * z`
(`z` upward, `rho0, g > 0`), the vertical density gradient is
`rho_z = -beta`, so the squared Brunt-Vaisala frequency is
`N^2 = -(g / rho0) * rho_z = g * beta / rho0`. Uniform density
(`beta = 0`) gives `N^2 = 0`, stable (`beta > 0`) gives `N^2 > 0`,
unstable (`beta < 0`) gives `N^2 < 0`. Density coefficients are fixed;
this is not a TEOS-10 derivation, and compressible in-situ gradients
require a potential-density / adiabatic correction.

## i. Overview

The gradient is the derivative of the linear profile; `N^2` follows
by algebra, and the sign classification follows from the signs of
`g, beta, rho0`.

## ii. Key results

- `EarthScience.boussinesq_density_deriv`: gradient of the linear profile.
- `EarthScience.brunt_vaisala_from_gradient`: `N^2` from the profile's
  actual vertical gradient `deriv (fun z => rho0 - beta * z) z`.
- `EarthScience.brunt_vaisala_sq_sign_ocean`: sign classification of `N^2`.

## iii. Table of contents

- A. Density gradient and Brunt-Vaisala frequency
- B. Stability signs

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed.,
  Cambridge University Press (2017), Chapter 2 (Effects of Rotation and
  Stratification): the Boussinesq approximation with a constant reference
  density `rho0`, and the buoyancy (Brunt-Vaisala) frequency
  `N^2 = -(g / rho0) * d rho / d z` with `z` pointing upward, so that
  `N^2 > 0` is statically stable and `N^2 < 0` is unstable.
- `HasDerivAt.const_sub` in Mathlib (derivative of a constant minus a function).
- `div_pos_iff` / `div_neg_iff` / `div_eq_zero_iff` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Density gradient and Brunt-Vaisala frequency -/

/-- The vertical gradient of the incompressible Boussinesq profile
`rho(z) = rho0 - beta * z` is `-beta` everywhere. -/
theorem boussinesq_density_deriv {rho0 beta : ℝ} (z : ℝ) :
    HasDerivAt (fun z => rho0 - beta * z) (-beta) z := by
  have h := HasDerivAt.const_sub rho0 ((hasDerivAt_id' z).const_mul beta)
  rwa [mul_one] at h

/-- `N^2 = -(g / rho0) * rho_z = g * beta / rho0` for the profile above,
where `rho_z = deriv (fun z => rho0 - beta * z) z` is its vertical
gradient at height `z` (equal to `-beta` by `boussinesq_density_deriv`). -/
theorem brunt_vaisala_from_gradient {g beta rho0 : ℝ} (z : ℝ) :
    -(g / rho0) * deriv (fun z => rho0 - beta * z) z = g * beta / rho0 := by
  rw [(boussinesq_density_deriv z).deriv]
  ring

/-! ## B. Stability signs -/

/-- Sign classification of `N^2 = g * beta / rho0` for `g, rho0 > 0`:
uniform density (`beta = 0`) gives `N^2 = 0`, stable (`beta > 0`) gives
`N^2 > 0`, unstable (`beta < 0`) gives `N^2 < 0`. -/
theorem brunt_vaisala_sq_sign_ocean {g beta rho0 : ℝ} (hg : 0 < g) (hrho : 0 < rho0) :
    (0 < g * beta / rho0 ↔ 0 < beta) ∧ (g * beta / rho0 = 0 ↔ beta = 0) ∧
      (g * beta / rho0 < 0 ↔ beta < 0) := by
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hr0 : rho0 ≠ 0 := ne_of_gt hrho
  have hng : ¬ g < 0 := not_lt.mpr hg.le
  have hnr : ¬ rho0 < 0 := not_lt.mpr hrho.le
  refine ⟨?_, ?_, ?_⟩
  · rw [div_pos_iff, mul_pos_iff, mul_neg_iff]
    simp [hg, hrho, hng, hnr]
  · rw [div_eq_zero_iff, mul_eq_zero]
    simp [hg0, hr0]
  · rw [div_neg_iff, mul_pos_iff, mul_neg_iff]
    simp [hg, hrho, hng, hnr]

end EarthScience

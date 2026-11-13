/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory intervalIntegral

/-!
# Integrated outgoing blackbody flux

A blackbody at temperature `T` emits outgoing flux `σ T⁴`
(Stefan-Boltzmann, with `σ ≥ 0`). A Lambertian surface has intensity
`σ T⁴ / π`; integrating that intensity over the outgoing hemisphere,
with the `cos θ` projection factor and the azimuthal factor `2π sin θ`,
recovers the adopted law `σ T⁴`.

## i. Overview

The integrand equals `σ T⁴ * 2 sin θ cos θ` after cancelling `π`, and
`∫₀^{π/2} 2 sin θ cos θ dθ = [sin² θ]₀^{π/2} = 1`. Nonnegativity is
`σ ≥ 0` times `T⁴ ≥ 0`.

## ii. Key results

- `EarthScience.integrated_blackbody_flux_eq`: hemispheric integration
  gives `σ T⁴`.
- `EarthScience.integrated_blackbody_flux_nonneg`: the flux is
  nonnegative for `σ ≥ 0`.

## iii. Table of contents

- A. Hemispheric integration

## iv. References

- `integral_sin_mul_cos₁` in Mathlib.
- `intervalIntegral.integral_const_mul` in Mathlib.

## A. Hemispheric integration
-/

@[expose] public section

namespace EarthScience

/-- Integrated outgoing blackbody flux: hemispheric integration of the
Lambertian intensity `σ T⁴ / π` with the `cos θ` projection and the
azimuthal factor `2π sin θ` gives the adopted Stefan-Boltzmann law
`σ T⁴`. -/
theorem integrated_blackbody_flux_eq {σ T : ℝ} :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), (σ * T ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ)
      = σ * T ^ 4 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfun : (fun θ : ℝ => (σ * T ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ))
      = fun θ : ℝ => (σ * T ^ 4) * (2 * (Real.sin θ * Real.cos θ)) := by
    funext θ
    field_simp
  rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_mul_cos₁, Real.sin_pi_div_two, Real.sin_zero]
  ring

/-- The integrated blackbody flux is nonnegative for `σ ≥ 0`. -/
theorem integrated_blackbody_flux_nonneg {σ T : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ σ * T ^ 4 := by
  apply mul_nonneg hσ
  positivity

end EarthScience

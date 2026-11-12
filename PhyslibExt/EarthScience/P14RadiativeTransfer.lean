/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Absorption-only radiative transfer: Beer–Lambert law (P14)

## i. Overview

In an absorption-only ray with constant absorption coefficient
`κ ≥ 0` and no emission or scattering, the radiance
`I(s) = I0 * exp(-κ * s)` solves `I' = -κ * I` with `I(0) = I0`.
Here `κ` has units of inverse length, the optical depth `κ * s` is
dimensionless, and radiance is distinct from irradiance. Radiation
energy laws are separate model assumptions.

## ii. Key results

- `EarthScience.p14_beer_lambert_initial`: `I(0) = I0`.
- `EarthScience.p14_beer_lambert_hasDerivAt`: `I' = -κ * I`.
- `EarthScience.p14_beer_lambert_nonneg`: `I ≥ 0` for `I0 ≥ 0`.
- `EarthScience.p14_beer_lambert_witness`: `I0 = 1, κ = 1` gives `I(1) = exp(-1)`.
- `EarthScience.p14_beer_lambert_no_absorption`: `κ = 0` gives constant `I`.

## iii. Table of contents

- A. Initial value and ODE
- B. Nonnegativity, witness, and no-absorption case

## iv. References

- `HasDerivAt.exp`, `HasDerivAt.const_mul` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Absorption-only ray: `I(s) = I0 * exp(-kappa * s)` satisfies `I(0) = I0`. -/
theorem p14_beer_lambert_initial {I0 κ : ℝ} :
    I0 * Real.exp (-κ * 0) = I0 := by
  simp

/-- Absorption-only ray: `I(s) = I0 * exp(-kappa * s)` solves `I' = -kappa * I`. -/
theorem p14_beer_lambert_hasDerivAt {I0 κ : ℝ} (s : ℝ) :
    HasDerivAt (fun s => I0 * Real.exp (-κ * s)) (-κ * (I0 * Real.exp (-κ * s))) s := by
  have h1 : HasDerivAt (fun s : ℝ => -κ * s) (-κ) s := by
    simpa using (hasDerivAt_id s).const_mul (-κ)
  have h2 := h1.exp
  have h3 := h2.const_mul I0
  convert h3 using 1
  ring

/-- Absorption-only ray: the solution is nonnegative for `I0 >= 0`. -/
theorem p14_beer_lambert_nonneg {I0 κ : ℝ} (hI0 : 0 ≤ I0) (s : ℝ) :
    0 ≤ I0 * Real.exp (-κ * s) := by
  exact mul_nonneg hI0 (Real.exp_nonneg _)

/-- Non-vacuous witness: `I0 = 1, kappa = 1` gives `I(0) = 1` and `I(1) = exp(-1)`. -/
theorem p14_beer_lambert_witness :
    (1 : ℝ) * Real.exp (-(1 : ℝ) * 0) = 1 ∧
    (1 : ℝ) * Real.exp (-(1 : ℝ) * 1) = Real.exp (-1) := by
  constructor
  · simp
  · norm_num

/-- Degenerate case `kappa = 0`: no absorption, intensity is constant. -/
theorem p14_beer_lambert_no_absorption {I0 : ℝ} (s : ℝ) :
    I0 * Real.exp (-(0 : ℝ) * s) = I0 := by
  simp

end EarthScience

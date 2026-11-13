/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Equilibrium tidal forcing and resonant response

## i. Overview

For the forced damped oscillator `x'' + 2γx' + ω₀²x = F cos(ωt)` with `γ > 0`, `ω₀ > 0`, `ω ≥ 0`,
  the harmonic steady-state coefficients `A = F(ω₀² - ω²)/D`, `B = F(2γω)/D` with `D = (ω₀² - ω²)²
  + (2γω)²` give amplitude `|F| / √D`. The oscillator equation is proved from the harmonic
  derivative formulas of `A cos(ωt) + B sin(ωt)`; this is a toy dynamical tide, not an equilibrium
  astronomical prediction.

## ii. Key results

- `EarthScience.damped_oscillator_coefficients`: the coefficient equations.
- `EarthScience.damped_oscillator_amplitude`: amplitude `|F| / √D`.
- `EarthScience.damped_oscillator_ode`: the harmonic function satisfies the oscillator equation.

## iii. Table of contents

- A. Steady-state coefficients and amplitude
- B. Oscillator equation

## iv. References

- `Real.sqrt_div`, `Real.sqrt_sq_eq_abs` in Mathlib.
-/

@[expose] public section

namespace EarthScience

private theorem damped_oscillator_coefficients_aux {F a b : ℝ}
    (hD : a ^ 2 + b ^ 2 ≠ 0) :
    a * (F * a / (a ^ 2 + b ^ 2)) + b * (F * b / (a ^ 2 + b ^ 2)) = F ∧
    a * (F * b / (a ^ 2 + b ^ 2)) - b * (F * a / (a ^ 2 + b ^ 2)) = 0 := by
  constructor
  · field_simp
  · field_simp
    ring

/-- Forced damped-oscillator steady-state coefficients: with
`D = (ω₀² - ω²)² + (2γω)² ≠ 0`, `A = F * (ω₀² - ω²) / D` and
`B = F * (2γω) / D` satisfy the two coefficient equations
`(ω₀² - ω²) * A + 2γω * B = F` and `(ω₀² - ω²) * B - 2γω * A = 0`. -/
theorem damped_oscillator_coefficients {F γ ω₀ ω : ℝ}
    (hD : (ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2 ≠ 0) :
    (ω₀ ^ 2 - ω ^ 2) * (F * (ω₀ ^ 2 - ω ^ 2) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2)) +
      2 * γ * ω * (F * (2 * γ * ω) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2)) = F ∧
    (ω₀ ^ 2 - ω ^ 2) * (F * (2 * γ * ω) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2)) -
      2 * γ * ω * (F * (ω₀ ^ 2 - ω ^ 2) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2)) = 0 := by
  exact damped_oscillator_coefficients_aux hD

private theorem damped_oscillator_amplitude_aux {F a b : ℝ}
    (hD : 0 < a ^ 2 + b ^ 2) :
    Real.sqrt ((F * a / (a ^ 2 + b ^ 2)) ^ 2 + (F * b / (a ^ 2 + b ^ 2)) ^ 2) =
    |F| / Real.sqrt (a ^ 2 + b ^ 2) := by
  have hDne : a ^ 2 + b ^ 2 ≠ 0 := ne_of_gt hD
  have hsq : (F * a / (a ^ 2 + b ^ 2)) ^ 2 + (F * b / (a ^ 2 + b ^ 2)) ^ 2 =
      F ^ 2 / (a ^ 2 + b ^ 2) := by
    field_simp
  rw [hsq, Real.sqrt_div (sq_nonneg F) _, Real.sqrt_sq_eq_abs]

/-- Harmonic amplitude: with `D = (ω₀² - ω²)² + (2γω)² > 0` and `A, B` as
above, `Real.sqrt (A ^ 2 + B ^ 2) = |F| / Real.sqrt D`. -/
theorem damped_oscillator_amplitude {F γ ω₀ ω : ℝ}
    (hD : 0 < (ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2) :
    Real.sqrt ((F * (ω₀ ^ 2 - ω ^ 2) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2)) ^ 2 +
      (F * (2 * γ * ω) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2)) ^ 2) =
    |F| / Real.sqrt ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2) := by
  exact damped_oscillator_amplitude_aux hD

/-- A harmonic function with the coefficient values above and derivative
formulas `x' = -Aω sin(ωt) + Bω cos(ωt)`, `x'' = -ω²x` (the derivative
formulas of `A cos(ωt) + B sin(ωt)`) satisfies the forced oscillator
equation `x'' + 2γx' + ω₀²x = F cos(ωt)` at every `t`. -/
theorem damped_oscillator_ode {F γ ω₀ ω : ℝ} (x : ℝ → ℝ) (t : ℝ)
    (hD : (ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2 ≠ 0)
    (hx : x t = F * (ω₀ ^ 2 - ω ^ 2) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2) *
        Real.cos (ω * t) +
      F * (2 * γ * ω) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2) *
        Real.sin (ω * t))
    (hx' : deriv x t = -(F * (ω₀ ^ 2 - ω ^ 2) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2)) * ω *
        Real.sin (ω * t) +
      (F * (2 * γ * ω) / ((ω₀ ^ 2 - ω ^ 2) ^ 2 + (2 * γ * ω) ^ 2)) * ω *
        Real.cos (ω * t))
    (hx'' : deriv (deriv x) t = -ω ^ 2 * x t) :
    deriv (deriv x) t + 2 * γ * deriv x t + ω₀ ^ 2 * x t =
      F * Real.cos (ω * t) := by
  have h := damped_oscillator_coefficients (F := F) hD
  obtain ⟨h1, h2⟩ := h
  rw [hx'', hx, hx']
  linear_combination h1 * Real.cos (ω * t) + h2 * Real.sin (ω * t)

end EarthScience

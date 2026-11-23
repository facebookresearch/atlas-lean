/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.IsothermalAtmosphericPressure

/-!
# Isothermal-atmosphere checks

Concrete consumers of
`PhyslibExt.EarthScience.IsothermalAtmosphericPressure`, with
`p0 = g = R = T = 1`, so `p(z) = exp (-z)`: `p(0) = 1`, `p(1) = 1 / exp 1`,
`p(1) < p(0)`, `p(5) > 0`, and `p'(0) = -1`, each from its named lemma.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Surface value and scale height
- B. Positivity and strict decrease
- C. Derivative at the surface
- D. Combined theorem shape

## iv. References

- `PhyslibExt.EarthScience.IsothermalAtmosphericPressure`
-/

open EarthScience

/-! ## A. Surface value and scale height -/

/-- The profile is `exp (-z)` for `p0 = g = R = T = 1`. -/
example (z : ℝ) : isothermalPressure 1 1 1 1 z = Real.exp (-z) := by
  simp [isothermalPressure]

/-- Surface value: `p(0) = 1` for `p0 = g = R = T = 1`. -/
example : isothermalPressure 1 1 1 1 0 = 1 :=
  isothermalPressure_zero 1 1 1 1

/-- One scale height: `p(1) = 1 / exp 1` for `p0 = g = R = T = 1`. -/
example : isothermalPressure 1 1 1 1 1 = 1 / Real.exp 1 := by
  simpa using isothermalPressure_scaleHeight (1 : ℝ) (g := 1) (R := 1) (T := 1)
    one_ne_zero one_ne_zero one_ne_zero

/-! ## B. Positivity and strict decrease -/

/-- Positivity: `p(5) > 0` for `p0 = g = R = T = 1`. -/
example : 0 < isothermalPressure 1 1 1 1 5 :=
  isothermalPressure_pos one_pos 1 1 1 5

/-- Strict decrease: `p(1) < p(0)` for `p0 = g = R = T = 1`. -/
example : isothermalPressure 1 1 1 1 1 < isothermalPressure 1 1 1 1 0 :=
  isothermalPressure_strictAnti one_pos one_pos one_pos one_pos zero_lt_one

/-! ## C. Derivative at the surface -/

/-- Hydrostatic slope at `z = 0` for `p0 = g = R = T = 1`: `p'(0) = -1`. -/
example : HasDerivAt (isothermalPressure 1 1 1 1) (-1) 0 := by
  convert hasDerivAt_isothermalPressure 1 1 1 1 0 using 1
  rw [isothermalPressure_zero]
  norm_num

/-! ## D. Combined theorem shape -/

/-- Public shape of the combined isothermal-atmosphere theorem. -/
example {p0 g R T : ℝ} (hp0 : 0 < p0) (hg : 0 < g) (hR : 0 < R) (hT : 0 < T) :
    (∀ z : ℝ, HasDerivAt (fun ζ : ℝ => p0 * Real.exp (-g * ζ / (R * T)))
        (-(p0 * Real.exp (-g * z / (R * T)) / (R * T)) * g) z) ∧
      (p0 * Real.exp (-g * (0 : ℝ) / (R * T)) = p0) ∧
      (∀ z : ℝ, 0 < p0 * Real.exp (-g * z / (R * T))) ∧
      (∀ z₁ z₂ : ℝ, z₁ < z₂ →
        p0 * Real.exp (-g * z₂ / (R * T)) < p0 * Real.exp (-g * z₁ / (R * T))) ∧
      (p0 * Real.exp (-g * (R * T / g) / (R * T)) = p0 / Real.exp 1) :=
  isothermal_atmospheric_pressure hp0 hg hR hT

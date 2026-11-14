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
`p(1) < p(0)`, `p(5) > 0`, and the derivative at `0` from the theorem.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Surface value and scale height
- B. Positivity and strict decrease
- C. Derivative at the surface
- D. Public theorem shape

## iv. References

- `PhyslibExt.EarthScience.IsothermalAtmosphericPressure`
-/

/-! ## A. Surface value and scale height -/

/-- Surface value: `p(0) = 1` for `p0 = g = R = T = 1`. -/
example : (1 : ℝ) * Real.exp (-1 * (0 : ℝ) / (1 * 1)) = 1 :=
  (EarthScience.isothermal_atmospheric_pressure (p0 := (1 : ℝ)) (g := (1 : ℝ))
    (R := (1 : ℝ)) (T := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).2.1

/-- One scale height: `p(1) = 1 / exp 1` for `p0 = g = R = T = 1`. -/
example : (1 : ℝ) * Real.exp (-1 * (1 * 1 / 1) / (1 * 1)) = 1 / Real.exp 1 :=
  (EarthScience.isothermal_atmospheric_pressure (p0 := (1 : ℝ)) (g := (1 : ℝ))
    (R := (1 : ℝ)) (T := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).2.2.2.2

/-! ## B. Positivity and strict decrease -/

/-- Positivity: `p(5) > 0` for `p0 = g = R = T = 1`. -/
example : 0 < (1 : ℝ) * Real.exp (-1 * (5 : ℝ) / (1 * 1)) :=
  (EarthScience.isothermal_atmospheric_pressure (p0 := (1 : ℝ)) (g := (1 : ℝ))
    (R := (1 : ℝ)) (T := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).2.2.1 5

/-- Strict decrease: `p(1) < p(0)` for `p0 = g = R = T = 1`. -/
example : (1 : ℝ) * Real.exp (-1 * (1 : ℝ) / (1 * 1)) <
    (1 : ℝ) * Real.exp (-1 * (0 : ℝ) / (1 * 1)) :=
  (EarthScience.isothermal_atmospheric_pressure (p0 := (1 : ℝ)) (g := (1 : ℝ))
    (R := (1 : ℝ)) (T := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).2.2.2.1 0 1 (by norm_num)

/-! ## C. Derivative at the surface -/

/-- Derivative at `z = 0` for `p0 = g = R = T = 1`, as given by the theorem. -/
example : HasDerivAt (fun ζ : ℝ => (1 : ℝ) * Real.exp (-1 * ζ / (1 * 1)))
    (-((1 : ℝ) * Real.exp (-1 * (0 : ℝ) / (1 * 1)) / (1 * 1)) * 1) 0 :=
  (EarthScience.isothermal_atmospheric_pressure (p0 := (1 : ℝ)) (g := (1 : ℝ))
    (R := (1 : ℝ)) (T := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).1 0

/-! ## D. Public theorem shape -/

/-- Public shape of the isothermal-atmosphere theorem. -/
example {p0 g R T : ℝ} (hp0 : 0 < p0) (hg : 0 < g) (hR : 0 < R) (hT : 0 < T) :
    (∀ z : ℝ, HasDerivAt (fun ζ : ℝ => p0 * Real.exp (-g * ζ / (R * T)))
        (-(p0 * Real.exp (-g * z / (R * T)) / (R * T)) * g) z) ∧
      (p0 * Real.exp (-g * (0 : ℝ) / (R * T)) = p0) ∧
      (∀ z : ℝ, 0 < p0 * Real.exp (-g * z / (R * T))) ∧
      (∀ z₁ z₂ : ℝ, z₁ < z₂ →
        p0 * Real.exp (-g * z₂ / (R * T)) < p0 * Real.exp (-g * z₁ / (R * T))) ∧
      (p0 * Real.exp (-g * (R * T / g) / (R * T)) = p0 / Real.exp 1) :=
  EarthScience.isothermal_atmospheric_pressure hp0 hg hR hT

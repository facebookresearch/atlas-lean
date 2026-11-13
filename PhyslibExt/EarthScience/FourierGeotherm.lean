/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.HeatConduction

/-!
# Capstone: conductive geotherm and cooling scale

## i. Overview

Synthetic constant-property slab; sign convention `flux = -k * dT / dz`
with depth/height coordinate `z` and temperature `T(z)`; boundary
temperatures are the profile values at the slab ends. A
zero-production geotherm with `k = 3 W / (m K)` and absolute flux
`0.06 W / m²` has gradient magnitude `0.02 K / m`. Numerical equality
for the stated rational inputs, not an empirical thermal profile.
The profile `T(z) = T₀ - (2 / 100) * z` is the steady slab profile of
`PhyslibExt.EarthScience.HeatConduction` with `L = 100` and
`TL = T₀ - 2`; its derivative and second derivative are specializations
of that API.

## ii. Key results

- `EarthScience.fourier_gradient_magnitude`: `|flux| = 0.06, k = 3` forces
  `|grad| = 0.02`.
- `EarthScience.geotherm_linear_profile_flux`: the linear profile
  `T(z) = T₀ - (2 / 100) * z` has derivative `-(2 / 100)` and flux `6 / 100`.
- `EarthScience.geotherm_deriv_const`: the profile's derivative is the
  constant `-(2 / 100)`.
- `EarthScience.geotherm_second_derivative_zero`: the profile's second
  derivative is `0` (zero internal heat production).

## iii. Table of contents

- A. Gradient magnitude, linear profile, and zero production

## iv. References

- `EarthScience.hasDerivAt_slab_profile` and
  `EarthScience.slab_profile_second_deriv` in
  `PhyslibExt.EarthScience.HeatConduction`.

## A. Gradient magnitude, linear profile, and zero production
-/

@[expose] public section

namespace EarthScience

/-- Capstone (conductive geotherm): Fourier's law `flux = -k * grad`
with `k = 3` and `|flux| = 0.06` forces `|grad| = 0.02`. -/
theorem fourier_gradient_magnitude {grad : ℝ} (h : |-(3 : ℝ) * grad| = 6 / 100) :
    |grad| = 2 / 100 := by
  have h1 : |-(3 : ℝ)| = 3 := by norm_num
  rw [abs_mul, h1] at h
  linarith

/-- The geotherm profile is the slab profile `T0 + (TL - T0) * z / L` of
`PhyslibExt.EarthScience.HeatConduction` with `T0 = T₀`, `TL = T₀ - 2`,
and `L = 100`. -/
private lemma geotherm_profile_eq_slab (T₀ : ℝ) :
    (fun z : ℝ => T₀ - (2 / 100 : ℝ) * z) = fun z => T₀ + (T₀ - 2 - T₀) * z / 100 := by
  funext z
  ring

/-- The linear profile `T(z) = T₀ - (2 / 100) * z` has derivative
`-(2 / 100)` everywhere, so with `k = 3` its conductive flux is
`-k * T' = 6 / 100`. The derivative is `EarthScience.hasDerivAt_slab_profile`
with `L = 100` and `TL = T₀ - 2`. -/
theorem geotherm_linear_profile_flux {T₀ z : ℝ} :
    HasDerivAt (fun z => T₀ - (2 / 100 : ℝ) * z) (-(2 / 100 : ℝ)) z ∧
      -(3 : ℝ) * (-(2 / 100 : ℝ)) = 6 / 100 := by
  have h := hasDerivAt_slab_profile (T0 := T₀) (TL := T₀ - 2) (L := 100) (by norm_num) z
  rw [← geotherm_profile_eq_slab] at h
  exact ⟨h.congr_deriv (by ring), by norm_num⟩

/-- The linear profile's derivative is the constant `-(2 / 100)` at
every point. -/
theorem geotherm_deriv_const {T₀ : ℝ} :
    ∀ z : ℝ, deriv (fun z => T₀ - (2 / 100 : ℝ) * z) z = -(2 / 100 : ℝ) := by
  intro z
  exact (geotherm_linear_profile_flux (T₀ := T₀) (z := z)).1.deriv

/-- Zero-production check: the linear profile's second derivative is `0`
(no internal heat production in the slab). This is the first conjunct of
`EarthScience.slab_profile_second_deriv` with `L = 100` and `TL = T₀ - 2`. -/
theorem geotherm_second_derivative_zero {T₀ : ℝ} :
    ∀ z : ℝ, iteratedDeriv 2 (fun z => T₀ - (2 / 100 : ℝ) * z) z = 0 := by
  intro z
  rw [geotherm_profile_eq_slab]
  exact (slab_profile_second_deriv (T0 := T₀) (TL := T₀ - 2) (L := 100) (k := 3)
    (by norm_num) z).1

end EarthScience

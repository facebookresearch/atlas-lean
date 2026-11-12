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
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Capstone: conductive geotherm and cooling scale

## i. Overview

Synthetic constant-property slab; sign convention `flux = -k * dT / dz`
with depth/height coordinate `z` and temperature `T(z)`; boundary
temperatures are the profile values at the slab ends. A
zero-production geotherm with `k = 3 W / (m K)` and absolute flux
`0.06 W / m²` has gradient magnitude `0.02 K / m`. Numerical equality
for the stated rational inputs, not an empirical thermal profile.
This capstone is proved self-contained from Mathlib primitives; it
does not depend on any sibling development.

## ii. Key results

- `EarthScience.fourier_gradient_magnitude`: `|flux| = 0.06, k = 3` forces
  `|grad| = 0.02`.
- `EarthScience.geotherm_linear_profile_flux`: the linear profile
  `T(z) = T₀ - (2 / 100) * z` has derivative `-(2 / 100)` and flux `6 / 100`.
- `EarthScience.geotherm_second_derivative_zero`: the profile's gradient
  is constant (zero internal heat production).

## iii. Table of contents

- A. Gradient magnitude, linear profile, and zero production

## iv. References

- `HasDerivAt.const_mul`, `hasDerivAt_id`, `hasDerivAt_const` in Mathlib.

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

/-- The linear profile `T(z) = T₀ - (2 / 100) * z` has derivative
`-(2 / 100)` everywhere, so with `k = 3` its conductive flux is
`-k * T' = 6 / 100`. -/
theorem geotherm_linear_profile_flux {T₀ z : ℝ} :
    HasDerivAt (fun z => T₀ - (2 / 100 : ℝ) * z) (-(2 / 100 : ℝ)) z ∧
      -(3 : ℝ) * (-(2 / 100 : ℝ)) = 6 / 100 := by
  have hmul : HasDerivAt (fun z : ℝ => (2 / 100 : ℝ) * z) (2 / 100 : ℝ) z := by
    simpa using (hasDerivAt_id z).const_mul (2 / 100 : ℝ)
  have hderiv : HasDerivAt (fun z : ℝ => T₀ - (2 / 100 : ℝ) * z) (0 - (2 / 100 : ℝ)) z :=
    (hasDerivAt_const z T₀).sub hmul
  have hderiv' : HasDerivAt (fun z : ℝ => T₀ - (2 / 100 : ℝ) * z) (-(2 / 100 : ℝ)) z := by
    simpa using hderiv
  exact ⟨hderiv', by norm_num⟩

/-- Zero-production check: the linear profile's gradient is constant,
so its second derivative is `0` (no internal heat production in the
slab). Stated as: the derivative function is constant `-(2 / 100)`. -/
theorem geotherm_second_derivative_zero {T₀ : ℝ} :
    ∀ z : ℝ, deriv (fun z => T₀ - (2 / 100 : ℝ) * z) z = -(2 / 100 : ℝ) := by
  intro z
  exact (geotherm_linear_profile_flux (T₀ := T₀) (z := z)).1.deriv

end EarthScience

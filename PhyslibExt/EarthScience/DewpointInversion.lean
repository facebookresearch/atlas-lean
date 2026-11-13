/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Dewpoint inversion is unique

## i. Overview

A dewpoint inversion is unique on the monotone range `T > 0`: for the
saturation law `es(T) = es0 * exp ((L / Rv) * (1 / T0 - 1 / T))` with
`es0, L, Rv > 0`, if `es(T₁) = es(T₂)` with `T₁, T₂ > 0` then
`T₁ = T₂`. Equivalently, `es` is injective on `Set.Ioi 0`. This is the
injectivity / uniqueness companion to the strict monotonicity of the
same saturation law proved in the saturation-pressure module: the
monotonicity statement there does not state uniqueness of the
inversion, and the inversion is the statement used when a measured
vapour pressure is inverted to a dewpoint temperature. The proof
cancels the positive factor `es0`, applies injectivity of `exp`,
cancels the positive factor `L / Rv`, and inverts `1 / T`.

## ii. Key results

- `EarthScience.dewpoint_inversion_unique`: equal saturation pressures
  at positive temperatures imply equal temperatures.

## iii. Table of contents

- A. Uniqueness of the dewpoint inversion

## iv. References

- `Real.exp_injective`, `inv_injective` in Mathlib.
- `mul_left_cancel₀`, `div_pos` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Uniqueness of the dewpoint inversion -/

set_option linter.unusedVariables false in
/-- A dewpoint inversion is unique on the monotone range `T > 0`: for
the saturation law `es(T) = es0 * exp ((L / Rv) * (1 / T0 - 1 / T))`
with `es0, L, Rv > 0`, if `es(T₁) = es(T₂)` with `T₁, T₂ > 0` then
`T₁ = T₂`. Equivalently `es` is injective on `Set.Ioi 0`. -/
theorem dewpoint_inversion_unique
    {es0 L Rv T0 : ℝ} (hes0 : 0 < es0) (hL : 0 < L) (hRv : 0 < Rv)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (h : es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T₁))
      = es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T₂))) :
    T₁ = T₂ := by
  have hexp : Real.exp ((L / Rv) * (1 / T0 - 1 / T₁))
      = Real.exp ((L / Rv) * (1 / T0 - 1 / T₂)) :=
    mul_left_cancel₀ hes0.ne' h
  have harg : (L / Rv) * (1 / T0 - 1 / T₁) = (L / Rv) * (1 / T0 - 1 / T₂) :=
    Real.exp_injective hexp
  have hc : (0 : ℝ) < L / Rv := div_pos hL hRv
  have hsub : (1 / T0 - 1 / T₁) = (1 / T0 - 1 / T₂) :=
    mul_left_cancel₀ hc.ne' harg
  have hdiv : (1 : ℝ) / T₁ = 1 / T₂ := by linarith
  rw [one_div, one_div] at hdiv
  exact inv_injective hdiv

end EarthScience

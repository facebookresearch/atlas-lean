/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Saturation vapour pressure: Clausius-Clapeyron derivative and strict increase

## i. Overview

For `es(T) = es0 * exp ((L / Rv) * (1 / T0 - 1 / T))` with
`es0, L, Rv, T0 > 0`, the Clausius-Clapeyron derivative is
`d(es) / dT = es(T) * L / (Rv * T ^ 2) > 0`, so saturation pressure is
strictly increasing on positive temperatures. This is the exact
constant-latent-heat ideal-vapour model with negligible condensed-phase
volume adopted, not a finite-error approximation theorem; `es` is a
pressure, `L` and `Rv` consistently mass-specific, the exponent dimensionless.

## ii. Key results

- `EarthScience.hasDerivAt_saturation_pressure`: the derivative formula.
- `EarthScience.saturation_pressure_deriv_pos`: the derivative is positive.
- `EarthScience.saturation_pressure_strictMono`: `es` is strictly increasing
  on positive temperatures.

## iii. Table of contents

- A. Derivative of saturation pressure
- B. Positivity and strict monotonicity

## iv. References

- `HasDerivAt.exp`, `hasDerivAt_inv`, `Real.exp_strictMono` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Saturation vapour pressure `es(T) = es0 * exp ((L / Rv) * (1 / T0 - 1 / T))`
has derivative `es(T) * L / (Rv * T ^ 2)` at `T > 0`. -/
theorem hasDerivAt_saturation_pressure {es0 L Rv T0 : ℝ} {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun T => es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T)))
      ((es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T))) * L / (Rv * T ^ 2)) T := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have h_inv : HasDerivAt (fun T : ℝ => (1:ℝ) / T) (-((T ^ 2)⁻¹)) T := by
    simpa only [one_div] using hasDerivAt_inv hTne
  have h_sub : HasDerivAt (fun T : ℝ => (1:ℝ) / T0 - 1 / T) ((T ^ 2)⁻¹) T := by
    have h1 : HasDerivAt (fun _ : ℝ => (1:ℝ) / T0) 0 T := hasDerivAt_const T _
    have h2 := h1.sub h_inv
    have hderiv : (0:ℝ) - -((T ^ 2)⁻¹) = (T ^ 2)⁻¹ := by simp
    rw [hderiv] at h2
    exact h2
  have h_inner : HasDerivAt (fun T : ℝ => (L / Rv) * (1 / T0 - 1 / T))
      ((L / Rv) * (T ^ 2)⁻¹) T :=
    h_sub.const_mul _
  have h_exp : HasDerivAt (fun T : ℝ => Real.exp ((L / Rv) * (1 / T0 - 1 / T)))
      (Real.exp ((L / Rv) * (1 / T0 - 1 / T)) * ((L / Rv) * (T ^ 2)⁻¹)) T :=
    h_inner.exp
  have h_full : HasDerivAt (fun T : ℝ => es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T)))
      (es0 * (Real.exp ((L / Rv) * (1 / T0 - 1 / T)) * ((L / Rv) * (T ^ 2)⁻¹))) T :=
    h_exp.const_mul _
  have heq : es0 * (Real.exp ((L / Rv) * (1 / T0 - 1 / T)) * ((L / Rv) * (T ^ 2)⁻¹))
      = (es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T))) * L / (Rv * T ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [heq] at h_full
  exact h_full

/-- The saturation-pressure derivative is positive for positive parameters. -/
theorem saturation_pressure_deriv_pos {es0 L Rv T0 : ℝ} (hes0 : 0 < es0)
    (hL : 0 < L) (hRv : 0 < Rv) {T : ℝ} (hT : 0 < T) :
    0 < (es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T))) * L / (Rv * T ^ 2) := by
  have hexp : 0 < Real.exp ((L / Rv) * (1 / T0 - 1 / T)) := Real.exp_pos _
  have hT2 : 0 < T ^ 2 := pow_pos hT 2
  exact div_pos (mul_pos (mul_pos hes0 hexp) hL) (mul_pos hRv hT2)

/-- Saturation pressure is strictly increasing on positive temperatures. -/
theorem saturation_pressure_strictMono {es0 L Rv T0 : ℝ} (hes0 : 0 < es0)
    (hL : 0 < L) (hRv : 0 < Rv) :
    StrictMonoOn (fun T => es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T)))
      (Set.Ioi 0) := by
  have hc : 0 < L / Rv := div_pos hL hRv
  have h_inner : StrictMonoOn (fun T : ℝ => (1:ℝ) / T0 - 1 / T) (Set.Ioi 0) := by
    intro a ha b hb hab
    rw [Set.mem_Ioi] at ha hb
    have h : (1:ℝ) / b < 1 / a := (one_div_lt_one_div hb ha).mpr hab
    change (1:ℝ) / T0 - 1 / a < 1 / T0 - 1 / b
    linarith
  have h_scaled : StrictMonoOn (fun T : ℝ => (L / Rv) * (1 / T0 - 1 / T)) (Set.Ioi 0) := by
    intro a ha b hb hab
    change (L / Rv) * (1 / T0 - 1 / a) < (L / Rv) * (1 / T0 - 1 / b)
    exact mul_lt_mul_of_pos_left (h_inner ha hb hab) hc
  have h_exp : StrictMonoOn (fun T : ℝ => Real.exp ((L / Rv) * (1 / T0 - 1 / T)))
      (Set.Ioi 0) := by
    intro a ha b hb hab
    change Real.exp ((L / Rv) * (1 / T0 - 1 / a)) < Real.exp ((L / Rv) * (1 / T0 - 1 / b))
    exact Real.exp_strictMono (h_scaled ha hb hab)
  intro a ha b hb hab
  change es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / a))
    < es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / b))
  exact mul_lt_mul_of_pos_left (h_exp ha hb hab) hes0

end EarthScience

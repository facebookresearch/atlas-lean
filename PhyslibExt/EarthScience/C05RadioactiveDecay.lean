/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import MathlibExt.Biology.Biophysics.CompartmentKinetics
/-!
# Radioactive decay and the unique positive half-life

For decay constant `λ > 0` and initial inventory `N0 > 0`,
`N(t) = N0 * exp(-λ*t)` solves `N' = -λ*N` and has the unique positive
half-life `log 2 / λ`.

## i. Overview

Constant single-parent decay law on `t ≥ 0`. Initial daughter and
branching are not needed for this result. The clock law is stipulated,
not empirically certified: this file proves the mathematics of the
exponential clock, not that any sample obeys it.

## ii. Key results

- `EarthScience.decay_hasDerivAt`: `N(t) = N0*exp(-λ*t)` satisfies `N' = -λ*N`.
- `EarthScience.decay_halfLife_value`: `N(log 2 / λ) = N0 / 2`.
- `EarthScience.decay_halfLife_unique`: any `t ≥ 0` with `N(t) = N0/2`
  equals `log 2 / λ`.

## iii. References

- `CompartmentKinetics.hasDerivAt_amount` and `CompartmentKinetics.amount_bolus` for
  the derivative: the decay law is the bolus case of the one-compartment amount.
- `CompartmentKinetics.amount_bolus_add_halfLife` for the half-life value.
- `Real.exp_log`, `Real.exp_injective` for the half-life uniqueness algebra.
-/

@[expose] public section

namespace EarthScience

/-- Radioactive decay: `N(t) = N0 * exp(-λ*t)` solves `N' = -λ*N`. This is the
bolus case (`R = 0`) of `CompartmentKinetics.hasDerivAt_amount`, via
`CompartmentKinetics.amount_bolus`; it is not a new exponential-decay derivative. -/
theorem decay_hasDerivAt (lam N0 t : ℝ) :
    HasDerivAt (fun t => N0 * Real.exp (-lam * t))
      (-lam * (N0 * Real.exp (-lam * t))) t := by
  have h := MathlibExt.Biology.Biophysics.CompartmentKinetics.hasDerivAt_amount lam 0 N0 t
  have hfun : (fun s => N0 * Real.exp (-lam * s)) =
      MathlibExt.Biology.Biophysics.CompartmentKinetics.amount lam 0 N0 := by
    funext s
    exact (MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus lam N0 s).symm
  rw [hfun]
  convert h using 1
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus]
  ring

set_option linter.unusedVariables false in
/-- At the half-life `log 2 / λ`, half the initial inventory remains. This is
`CompartmentKinetics.amount_bolus_add_halfLife` at time zero, via
`CompartmentKinetics.amount_bolus`. -/
theorem decay_halfLife_value (lam N0 : ℝ) (hlam : 0 < lam) (hN0 : 0 < N0) :
    N0 * Real.exp (-lam * (Real.log 2 / lam)) = N0 / 2 := by
  have h := MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus_add_halfLife
    (ne_of_gt hlam) N0 (0 : ℝ)
  simp only [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus,
    MathlibExt.Biology.Biophysics.CompartmentKinetics.halfLife, zero_add, mul_zero,
    Real.exp_zero, mul_one] at h
  exact h

set_option linter.unusedVariables false in
/-- The positive half-life is unique: any `t ≥ 0` with `N(t) = N0/2`
equals `log 2 / λ`. -/
theorem decay_halfLife_unique (lam N0 t : ℝ) (hlam : 0 < lam) (hN0 : 0 < N0)
    (ht : 0 ≤ t) (h : N0 * Real.exp (-lam * t) = N0 / 2) :
    t = Real.log 2 / lam := by
  have hN0' : N0 ≠ 0 := ne_of_gt hN0
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have h2 : N0 * Real.exp (-lam * t) = N0 * (1 / 2) := by
    rw [h]
    ring
  have hexp : Real.exp (-lam * t) = 1 / 2 := mul_left_cancel₀ hN0' h2
  have hexp2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  have harg : -lam * t = -Real.log 2 := Real.exp_injective (hexp.trans hexp2.symm)
  have hlamt : lam * t = Real.log 2 := by linarith
  rw [eq_div_iff hlam']
  linarith

end EarthScience

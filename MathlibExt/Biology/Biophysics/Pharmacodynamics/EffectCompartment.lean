/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Effect-compartment lag model

The effect concentration for plasma input with first-order lag:
its initial value, nonnegativity for nonnegative input, and the
zero-input case.
-/

@[expose] public section

open Real MeasureTheory

namespace MathlibExt.Biology.Biophysics.Pharmacodynamics.EffectCompartment

/-- The effect-compartment concentration with lag rate `ke0`,
plasma input `Cp`, and initial effect `Ce0`. -/
noncomputable def effectConc (ke0 Ce0 : ℝ) (Cp : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-ke0 * t) * Ce0 +
    ke0 * ∫ s in (0:ℝ)..t, Real.exp (-ke0 * (t - s)) * Cp s

/-- **Initial effect.** At time zero the effect is `Ce0`. -/
theorem effectConc_zero (ke0 Ce0 : ℝ) (Cp : ℝ → ℝ) :
    effectConc ke0 Ce0 Cp 0 = Ce0 := by
  unfold effectConc
  simp [intervalIntegral.integral_same]

/-- **Nonnegative effect.** For `ke0 > 0`, nonnegative plasma
input on `[0, t]`, and `Ce0 ≥ 0`, the effect at `t ≥ 0` is
nonnegative. -/
theorem effectConc_nonneg {ke0 Ce0 t : ℝ} {Cp : ℝ → ℝ} (hke : 0 < ke0)
    (hCe : 0 ≤ Ce0) (ht : 0 ≤ t) (hCp : ∀ s ∈ Set.Icc 0 t, 0 ≤ Cp s)
    (hInt : IntervalIntegrable (fun s => Real.exp (-ke0 * (t - s)) * Cp s)
      MeasureTheory.volume 0 t) :
    0 ≤ effectConc ke0 Ce0 Cp t := by
  have _ := hInt
  unfold effectConc
  apply add_nonneg
  · exact mul_nonneg (Real.exp_nonneg _) hCe
  · apply mul_nonneg (le_of_lt hke)
    apply intervalIntegral.integral_nonneg ht
    intro s hs
    exact mul_nonneg (Real.exp_nonneg _) (hCp s hs)

/-- **Zero input and zero initial effect give zero effect.** -/
theorem effectConc_zero_input (ke0 t : ℝ) :
    effectConc ke0 0 (fun _ => 0) t = 0 := by
  unfold effectConc
  simp

end MathlibExt.Biology.Biophysics.Pharmacodynamics.EffectCompartment

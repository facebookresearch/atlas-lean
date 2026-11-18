/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Biology.Dynamics.FeedForwardLoop

/-!
# Effect-compartment lag model

The effect concentration is the canonical relaxation
(variation-of-constants) solution with production `ke0 * Cp`:
it solves the lag equation `Ce' = ke0 * (Cp - Ce)`, starts at
`Ce0`, and stays nonnegative for nonnegative input.

## References

* The effect-compartment model with first-order equilibration
  `Ce' = ke0 * (Cp - Ce)` is the model of Sheiner, Stanski,
  Vozeh, Miller, and Ham, *Simultaneous modeling of
  pharmacokinetics and pharmacodynamics: application to
  d-tubocurarine*, Clin. Pharmacol. Ther. 25 (1979) 358-371.
-/

@[expose] public section

open Real MeasureTheory

namespace MathlibExt.Biology.Biophysics.Pharmacodynamics.EffectCompartment

/-- The effect-compartment concentration with lag rate `ke0`,
plasma input `Cp`, and initial effect `Ce0`, as the canonical
relaxation solution. -/
noncomputable def effectConc (ke0 Ce0 : ℝ) (Cp : ℝ → ℝ) (t : ℝ) : ℝ :=
  MathlibExt.Biology.Dynamics.FeedForwardLoop.relaxation ke0 (fun s => ke0 * Cp s) Ce0 t

/-- **Initial effect.** At time zero the effect is `Ce0`. -/
theorem effectConc_zero (ke0 Ce0 : ℝ) (Cp : ℝ → ℝ) :
    effectConc ke0 Ce0 Cp 0 = Ce0 := by
  unfold effectConc MathlibExt.Biology.Dynamics.FeedForwardLoop.relaxation
  simp [intervalIntegral.integral_same]

/-- **The lag equation.** Where the plasma input is continuous
and locally integrable, the effect solves
`Ce' = ke0 * (Cp - Ce)`. -/
theorem hasDerivAt_effectConc {ke0 Ce0 t : ℝ} {Cp : ℝ → ℝ}
    (hCp : ∀ a b, IntervalIntegrable Cp MeasureTheory.volume a b)
    (ht : ContinuousAt Cp t) :
    HasDerivAt (effectConc ke0 Ce0 Cp) (ke0 * (Cp t - effectConc ke0 Ce0 Cp t)) t := by
  have h := MathlibExt.Biology.Dynamics.FeedForwardLoop.hasDerivAt_relaxation
    (α := ke0) (P := fun s => ke0 * Cp s) Ce0
    (fun a b => IntervalIntegrable.const_mul (hCp a b) ke0)
    (ContinuousAt.const_mul ht ke0)
  have h2 : effectConc ke0 Ce0 Cp =
      MathlibExt.Biology.Dynamics.FeedForwardLoop.relaxation ke0 (fun s => ke0 * Cp s) Ce0 := rfl
  rw [h2]
  convert h using 1
  ring

/-- **Nonnegative effect.** For `ke0 > 0`, nonnegative plasma
input on `[0, t]`, and `Ce0 ≥ 0`, the effect at `t ≥ 0` is
nonnegative. -/
theorem effectConc_nonneg {ke0 Ce0 t : ℝ} {Cp : ℝ → ℝ} (hke : 0 < ke0)
    (hCe : 0 ≤ Ce0) (ht : 0 ≤ t) (hCp : ∀ s ∈ Set.Icc 0 t, 0 ≤ Cp s) :
    0 ≤ effectConc ke0 Ce0 Cp t := by
  unfold effectConc MathlibExt.Biology.Dynamics.FeedForwardLoop.relaxation
  apply add_nonneg
  · exact mul_nonneg hCe (Real.exp_nonneg _)
  · apply intervalIntegral.integral_nonneg ht
    intro s hs
    exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg hke.le (hCp s hs))

/-- **Zero input and zero initial effect give zero effect.** -/
theorem effectConc_zero_input (ke0 t : ℝ) :
    effectConc ke0 0 (fun _ => 0) t = 0 := by
  unfold effectConc MathlibExt.Biology.Dynamics.FeedForwardLoop.relaxation
  simp

end MathlibExt.Biology.Biophysics.Pharmacodynamics.EffectCompartment

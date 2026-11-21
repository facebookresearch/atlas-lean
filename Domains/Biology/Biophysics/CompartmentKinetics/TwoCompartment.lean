/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Two-compartment positivity

For the two-compartment bolus model with nonnegative rates and
dose, the peripheral amount in Duhamel (convolution) form is
nonnegative at nonnegative times: transferred mass decays without
sign change.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment

set_option linter.unusedVariables false in
/-- **Peripheral amount nonnegativity (Duhamel form).** With
nonnegative transfer `k12 ≥ 0`, elimination `k21 ≥ 0`, central rate
`k10 ≥ 0` and dose `D ≥ 0`, the peripheral amount at `a ≥ 0` in
Duhamel form,
`∫ s in 0..a, exp (-k21 (a - s)) * (k12 * D * exp (-(k10+k12) s))`,
is nonnegative: mass transferred in is nonnegative and decays
without sign change. -/
lemma peripheral_amount_nonneg {k10 k12 k21 D a : ℝ}
    (hk10 : 0 ≤ k10) (hk12 : 0 ≤ k12) (hk21 : 0 ≤ k21) (hD : 0 ≤ D)
    (ha : 0 ≤ a) :
    0 ≤ ∫ s in (0:ℝ)..a,
      Real.exp (-k21 * (a - s)) * (k12 * (D * Real.exp (-(k10 + k12) * s))) := by
  apply intervalIntegral.integral_nonneg ha
  intro s _
  apply mul_nonneg (Real.exp_nonneg _)
  apply mul_nonneg hk12
  apply mul_nonneg hD
  exact Real.exp_nonneg _

end MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment

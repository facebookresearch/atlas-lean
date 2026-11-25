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

For a two-compartment bolus model without return flow (the
peripheral compartment loses its content to outside the system)
and with nonnegative rates and dose, the peripheral amount in
Duhamel (convolution) form is nonnegative at nonnegative times:
transferred mass decays without sign change. With transfer back to
the central compartment (and positive transfer and dose) the Duhamel
integral is not the peripheral amount.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment

set_option linter.unusedVariables false in
/-- **Peripheral amount nonnegativity without return flow (Duhamel form).** With nonnegative
transfer `k12 ≥ 0`, peripheral loss rate `k21 ≥ 0`, central elimination `k10 ≥ 0` and dose `D ≥ 0`,
the Duhamel integral `∫ s in 0..a, exp (-k21 (a - s)) * (k12 * D * exp (-(k10+k12) s))` is
nonnegative at `a ≥ 0`: mass transferred in is nonnegative and decays without sign change. It is the
peripheral amount of a two-compartment model without return flow, whose central amount is
`D exp (-(k10+k12) s)` and whose peripheral compartment loses its content at rate `k21` to outside
the system. With transfer back to the central compartment at rate `k21 > 0` (with `k12 > 0` and
`D > 0`), as in the two-compartment generator, it is not the peripheral amount. -/
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

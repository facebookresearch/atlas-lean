/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-!
# Joint-hazard conditional-damage risk

## i. Overview

For a probability hazard law, a Markov damage kernel, and a
measurable nonnegative loss, the expected loss under the joint law
equals the iterated integral: conditional expected loss given the
hazard state, averaged over the hazard law.

## ii. Key results

- `HazardDamageRisk.risk_eq_iterated`: the joint/iterated identity.

## iii. Table of contents

- A. Risk identity

## iv. References

- Standard law-of-total-expectation for Markov kernels
  (composition-product of a measure with a kernel).

## A. Risk identity
-/

@[expose] public section

namespace HazardDamageRisk

/-- Joint-hazard conditional-damage risk: for a probability hazard
law `μ`, a Markov damage kernel `κ`, and a measurable nonnegative
loss `L`, the risk computed against the joint law `μ ⊗ₘ κ`
equals the iterated integral: first the conditional expected loss
given the hazard state, then the hazard average. -/
theorem risk_eq_iterated {Ω Γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (κ : ProbabilityTheory.Kernel Ω Γ)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : Ω × Γ → ℝ≥0∞) (hL : Measurable L) :
    ∫⁻ z, L z ∂(μ ⊗ₘ κ)
      = ∫⁻ ω, ∫⁻ γ, L (ω, γ) ∂(κ ω) ∂μ := by
  exact MeasureTheory.Measure.lintegral_compProd hL

end HazardDamageRisk

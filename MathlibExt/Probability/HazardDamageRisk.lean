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

- `HazardDamageRisk.risk`: expected loss under hazard then damage.
- `HazardDamageRisk.risk_eq_joint`: risk as expectation under the
  joint law.
- `HazardDamageRisk.risk_const`, `HazardDamageRisk.risk_mono`:
  constant-loss value and monotonicity.

## iii. Table of contents

- A. Risk identity

## iv. References

- Standard law-of-total-expectation for Markov kernels
  (composition-product of a measure with a kernel).

## A. Risk identity
-/

@[expose] public section

namespace HazardDamageRisk

/-- Joint-hazard conditional-damage risk: the expected loss of the
damage state drawn from the kernel `κ` at hazard state drawn from
`μ`. -/
noncomputable def risk {Ω Γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] (μ : MeasureTheory.Measure Ω)
    (κ : ProbabilityTheory.Kernel Ω Γ) (L : Ω × Γ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ γ, L (ω, γ) ∂(κ ω) ∂μ

/-- The risk equals the expected loss under the joint law
`μ ⊗ₘ κ`. -/
theorem risk_eq_joint {Ω Γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (κ : ProbabilityTheory.Kernel Ω Γ)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L : Ω × Γ → ℝ≥0∞) (hL : Measurable L) :
    risk μ κ L = ∫⁻ z, L z ∂(μ ⊗ₘ κ) := by
  unfold risk
  exact (MeasureTheory.Measure.lintegral_compProd hL).symm

/-- Constant loss: if the loss is constantly `c`, the risk is `c`
(the joint law of a probability hazard and a Markov damage kernel
is a probability law). -/
theorem risk_const {Ω Γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (κ : ProbabilityTheory.Kernel Ω Γ)
    [ProbabilityTheory.IsMarkovKernel κ] (c : ℝ≥0∞) :
    risk μ κ (fun _ => c) = c := by
  simp [risk]

/-- Monotonicity: a pointwise smaller loss has smaller risk. -/
theorem risk_mono {Ω Γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (κ : ProbabilityTheory.Kernel Ω Γ)
    [ProbabilityTheory.IsMarkovKernel κ]
    (L L' : Ω × Γ → ℝ≥0∞) (h : ∀ z, L z ≤ L' z) :
    risk μ κ L ≤ risk μ κ L' := by
  unfold risk
  exact MeasureTheory.lintegral_mono fun ω =>
    MeasureTheory.lintegral_mono fun γ => h (ω, γ)

end HazardDamageRisk

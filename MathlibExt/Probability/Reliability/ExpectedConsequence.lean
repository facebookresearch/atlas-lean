/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Expected consequence of a finite damage kernel

The expected consequence of a damage kernel averages an
extended-real loss first over damage states (through the
kernel) and then over the hazard law; the value may be
infinite and no finiteness is assumed. For finitely many
damage states the inner average is the finite sum of kernel
masses times losses, and the expected consequence is monotone
under pointwise larger losses.

## Main results

- `expectedConsequence_fintype`: the finite damage-state
  decomposition.
- `expectedConsequence_mono`: monotonicity in the loss.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Expected consequence of a damage kernel: first average the
loss over damage states for each hazard outcome, then average
over the hazard law. The value is extended-real and may be
infinite. -/
noncomputable def expectedConsequence {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β) (μ : Measure α)
    (L : β → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ b, L b ∂(κ a) ∂μ

/-- Finite damage-state decomposition: for finitely many damage
states, the expected consequence is the hazard average of the
finite state sum `∑ b, (κ a {b}) * L b`. -/
theorem expectedConsequence_fintype {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Fintype β]
    [MeasurableSingletonClass β]
    (κ : ProbabilityTheory.Kernel α β) (μ : Measure α)
    (L : β → ℝ≥0∞) :
    expectedConsequence κ μ L
      = ∫⁻ a, ∑ b, (κ a {b}) * L b ∂μ := by
  unfold expectedConsequence
  apply lintegral_congr
  intro a
  rw [lintegral_fintype]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

/-- Expected consequence is monotone under pointwise larger
nonnegative losses. -/
theorem expectedConsequence_mono {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β) (μ : Measure α)
    {L L' : β → ℝ≥0∞} (hL : ∀ b, L b ≤ L' b) :
    expectedConsequence κ μ L ≤ expectedConsequence κ μ L' := by
  unfold expectedConsequence
  exact lintegral_mono (fun a => lintegral_mono (fun b => hL b))

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Decision.Risk.Defs
public import MathlibExt.Probability.Statistics.EstimationRisk

import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# INF-00: deterministic-kernel risk bridge

Mathlib expresses the risk of an estimator through kernels: the data law is pushed through an
estimator kernel by `MeasureTheory.Measure.bind` (notation `κ ∘ₘ μ`), and
`ProbabilityTheory.avgRisk` averages the resulting risk against a prior. For a deterministic
estimator `δ`, i.e. the kernel `ProbabilityTheory.Kernel.deterministic δ hδ`, these expressions
are identified with Atlas's extended frequentist risk `frequentistRiskENN` and extended mean
squared error `meanSquaredErrorENN`; no competing notion of risk is introduced.

## Main statements

* `lintegral_deterministic_bind_eq_frequentistRiskENN`: fixed-law bridge.
* `avgRisk_deterministic_eq_lintegral_frequentistRiskENN`: Mathlib's average risk of a
  deterministic estimator is the prior integral of `frequentistRiskENN`.
* `lintegral_deterministic_bind_ofReal_sq_eq_meanSquaredErrorENN`: squared-error specialization.

`meanSquaredErrorENN` and `frequentistRiskENN` are imported from `EstimationRisk`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.EstimationRisk

@[expose] public section

/-- **Fixed-law deterministic-kernel bridge.**

Informal clause ↦ formal binder or hypothesis:
* `S` and `A` are measurable spaces ↦ `[MeasurableSpace S] [MeasurableSpace A]`;
* `Θ` is any type, with no measurability assumption ↦ `{Θ : Type*}`, no instance on `Θ`;
* `δ`, `P` and `ℓ` are fixed before the parameter is chosen ↦ they are bound before `θ`, so
  none of them depends on `θ`;
* a measurable estimator ↦ `δ : S → A` and `hδ : Measurable δ`;
* a frequentist family ↦ `P : Θ → ProbabilityMeasure S` (a plain function, not a kernel);
* an NNReal-valued loss ↦ `ℓ : Θ → A → NNReal`; a parameter ↦ `θ : Θ`;
* the only assumption: the loss section `a ↦ ((ℓ θ a : NNReal) : ℝ≥0∞)` is measurable ↦ `hℓ`
  (no joint measurability, finiteness or integrability);
* the bind of `(P θ : Measure S)` through Mathlib's deterministic kernel for `δ` ↦
  `(P θ : Measure S).bind (Kernel.deterministic δ hδ)`, i.e. `Kernel.deterministic δ hδ ∘ₘ P θ`;
* conclusion: the Lebesgue integral of the loss section under that law equals
  `frequentistRiskENN δ P ℓ θ`. -/
theorem lintegral_deterministic_bind_eq_frequentistRiskENN {Θ S A : Type*}
    [MeasurableSpace S] [MeasurableSpace A]
    (δ : S → A) (hδ : Measurable δ) (P : Θ → ProbabilityMeasure S)
    (ℓ : Θ → A → NNReal) (θ : Θ)
    (hℓ : Measurable fun a ↦ ((ℓ θ a : NNReal) : ℝ≥0∞)) :
    ∫⁻ a, ((ℓ θ a : NNReal) : ℝ≥0∞) ∂((P θ : Measure S).bind (Kernel.deterministic δ hδ)) =
      frequentistRiskENN δ P ℓ θ := by
  rw [frequentistRiskENN, Measure.deterministic_comp_eq_map hδ, lintegral_map hℓ hδ]

/-- **Mathlib average-risk bridge.**

Informal clause ↦ formal binder or hypothesis:
* `Θ`, `S` and `A` are measurable spaces ↦
  `[MeasurableSpace Θ] [MeasurableSpace S] [MeasurableSpace A]`;
* a Markov data-generating kernel ↦ `P : Kernel Θ S` with `[IsMarkovKernel P]`;
* a prior measure ↦ `π : Measure Θ` (no finiteness or probability assumption);
* a measurable estimator ↦ `δ : S → A` and `hδ : Measurable δ`;
* an NNReal-valued loss ↦ `ℓ : Θ → A → NNReal`;
* every loss section `a ↦ ((ℓ θ a : NNReal) : ℝ≥0∞)` is measurable ↦ `hℓ`
  (no joint measurability in `(θ, a)`);
* Mathlib's average risk for the coerced loss, the kernel `P`, the deterministic estimator kernel
  for `δ` and the prior `π` ↦
  `avgRisk (fun θ a ↦ ((ℓ θ a : NNReal) : ℝ≥0∞)) P (Kernel.deterministic δ hδ) π`;
* `P' θ`, the probability measure obtained from `P θ` by the Markov property ↦
  `⟨P θ, IsMarkovKernel.isProbabilityMeasure θ⟩ : ProbabilityMeasure S`, the only use of
  `[IsMarkovKernel P]`;
* conclusion: the average risk equals `∫⁻ θ, frequentistRiskENN δ P' ℓ θ ∂π`.

No σ-finiteness, standard Borel or countability assumption is made. -/
theorem avgRisk_deterministic_eq_lintegral_frequentistRiskENN {Θ S A : Type*}
    [MeasurableSpace Θ] [MeasurableSpace S] [MeasurableSpace A]
    (P : Kernel Θ S) [IsMarkovKernel P] (π : Measure Θ)
    (δ : S → A) (hδ : Measurable δ) (ℓ : Θ → A → NNReal)
    (hℓ : ∀ θ, Measurable fun a ↦ ((ℓ θ a : NNReal) : ℝ≥0∞)) :
    avgRisk (fun θ a ↦ ((ℓ θ a : NNReal) : ℝ≥0∞)) P (Kernel.deterministic δ hδ) π =
      ∫⁻ θ, frequentistRiskENN δ (fun θ ↦ ⟨P θ, IsMarkovKernel.isProbabilityMeasure θ⟩) ℓ θ ∂π := by
  rw [avgRisk]
  refine lintegral_congr fun θ ↦ ?_
  rw [Kernel.comp_apply]
  exact lintegral_deterministic_bind_eq_frequentistRiskENN δ hδ
    (fun θ ↦ ⟨P θ, IsMarkovKernel.isProbabilityMeasure θ⟩) ℓ θ (hℓ θ)

/-- **Squared-error specialization.**

Informal clause ↦ formal binder or hypothesis:
* `S` is a measurable space ↦ `[MeasurableSpace S]`;
* a measurable real estimator ↦ `W : S → ℝ` and `hW : Measurable W`;
* a probability law ↦ `μ : ProbabilityMeasure S`; a target value ↦ `θ : ℝ`;
* the squared-error loss `a ↦ ENNReal.ofReal ((a - θ) ^ 2)`, whose measurability is derived in the
  proof rather than assumed;
* the bind of `(μ : Measure S)` through the deterministic kernel for `W` ↦
  `(μ : Measure S).bind (Kernel.deterministic W hW)`;
* conclusion: the Lebesgue integral of the loss under that law equals `meanSquaredErrorENN W μ θ`.

No finite second moment or integrability is assumed: both sides live in `ℝ≥0∞` and may equal `∞`,
e.g. for an estimator that is not square-integrable. -/
theorem lintegral_deterministic_bind_ofReal_sq_eq_meanSquaredErrorENN {S : Type*}
    [MeasurableSpace S] (W : S → ℝ) (hW : Measurable W) (μ : ProbabilityMeasure S) (θ : ℝ) :
    ∫⁻ a, ENNReal.ofReal ((a - θ) ^ 2) ∂((μ : Measure S).bind (Kernel.deterministic W hW)) =
      meanSquaredErrorENN W μ θ := by
  have hloss : Measurable fun a : ℝ ↦ ENNReal.ofReal ((a - θ) ^ 2) :=
    ((measurable_id.sub_const θ).pow_const 2).ennreal_ofReal
  rw [meanSquaredErrorENN, Measure.deterministic_comp_eq_map hW, lintegral_map hloss hW]

end

end MathlibExt.Probability.Statistics.EstimationRisk

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.FiniteMixtureMoments
import Mathlib.Probability.Distributions.Bernoulli

/-!
# A shared-class Bernoulli sample

The latent coin selects either a constant zero or a fair Bernoulli component. Each
observation by itself is Bernoulli with success probability `1/4`. Redrawing the class
independently for each observation would give variance `3/32` for the average of two.
-/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.FiniteMixture

namespace MathlibExtTest.Probability.FiniteMixture

private noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

private noncomputable abbrev fair := bernoulliMeasure true false half

private noncomputable def component : Bool → Measure Bool
  | false => Measure.dirac false
  | true => fair

private instance (b : Bool) : IsProbabilityMeasure (component b) := by
  cases b <;> unfold component <;> infer_instance

private def bit (b : Bool) : ℝ := if b then 1 else 0

private theorem integral_fair (g : Bool → ℝ) :
    (∫ b, g b ∂fair) = (1 / 2 : ℝ) * g true + (1 / 2 : ℝ) * g false := by
  rw [integral_bernoulliMeasure]
  norm_num [half, smul_eq_mul]

private noncomputable def m (b : Bool) := ∫ s, bit s ∂component b

private noncomputable def v (b : Bool) := variance bit (component b)

private lemma between : variance m fair = 1 / 16 := by
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable]
  norm_num [integral_fair, m, component, bit]

private lemma within : (∫ b, v b ∂fair) = 1 / 8 := by
  rw [integral_fair]
  norm_num [v, component, variance_eq_integral Measurable.of_discrete.aemeasurable,
    integral_fair, bit]

private noncomputable def avg (n : ℕ) (z : Bool × (Fin n → Bool)) := (∑ i, bit (z.2 i)) / n

-- Both variance components are strictly positive. Independence under the one-observation
-- marginal would give the wrong second answer.
example : let P := fair ⊗ₘ sampleKernel 2 component
    covariance (fun z => m z.1) (avg 2) P = 1 / 16 ∧ variance (avg 2) P = 1 / 8 := by
  intro P
  have h := buhlmann_moments fair component bit 2 (by decide)
  change covariance (fun z => m z.1) (avg 2) P = variance m fair ∧
    variance (avg 2) P = variance m fair + (∫ b, v b ∂fair) / 2 at h
  rw [h.1, h.2, between, within]
  norm_num

-- At n = 1 there is no within-class variance reduction.
example : variance (avg 1) (fair ⊗ₘ sampleKernel 1 component) = 3 / 16 := by
  have h := (buhlmann_moments fair component bit 1 (by decide)).2
  change variance (avg 1) (fair ⊗ₘ sampleKernel 1 component) =
    variance m fair + (∫ b, v b ∂fair) / ((1 : ℕ) : ℝ) at h
  rw [h, between, within]
  norm_num

end MathlibExtTest.Probability.FiniteMixture

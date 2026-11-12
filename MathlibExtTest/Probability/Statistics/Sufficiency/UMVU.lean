/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.UMVU
public import MathlibExt.Probability.Statistics.Sufficiency.Complete

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Sufficiency.UMVU



open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.EstimationRisk



/-- Fixture A (through the main theorem): the Rao–Blackwell version of any measurable
unbiased estimator is unbiased, agrees a.e. with the conditional expectation
(the exposed Rao–Blackwell relation), and attains no larger variance than any
measurable unbiased finite-variance competitor. -/
example {Ω Θ τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {P : Θ → ProbabilityMeasure Ω} {S : Ω → τ}
    (hcomplete : MathlibExt.Probability.Statistics.Sufficiency.IsCompleteStatistic P S)
    (hS : MathlibExt.Probability.Statistics.Sufficiency.IsSufficient
      (MeasurableSpace.comap S ‹MeasurableSpace τ›) fun θ => ((P θ) : Measure Ω))
    (tgt : Θ → ℝ) {W : Ω → ℝ}
    (hunb : MathlibExt.Probability.Statistics.EstimationRisk.IsUnbiased W P tgt)
    (hWm : Measurable W)
    (hW : ∀ θ, MemLp W 2 ((P θ) : Measure Ω))
    {W' : Ω → ℝ}
    (hunb' : MathlibExt.Probability.Statistics.EstimationRisk.IsUnbiased W' P tgt)
    (hWm' : Measurable W') (hW' : ∀ θ, MemLp W' 2 ((P θ) : Measure Ω)) :
    ∃ φ : τ → ℝ, Measurable φ ∧
      MathlibExt.Probability.Statistics.EstimationRisk.IsUnbiased (fun ω => φ (S ω)) P tgt ∧
      (∀ θ, (fun ω => φ (S ω)) =ᵐ[((P θ) : Measure Ω)]
        (((P θ) : Measure Ω)[W | MeasurableSpace.comap S ‹MeasurableSpace τ›])) ∧
      ∀ θ, ProbabilityTheory.variance (fun ω => φ (S ω)) ((P θ) : Measure Ω) ≤
        ProbabilityTheory.variance W' ((P θ) : Measure Ω) := by
  obtain ⟨φ, hφ, hunbφ, haeφ, hopt⟩ :=
    MathlibExt.Probability.Statistics.Sufficiency.umvu_of_complete_sufficient
      hcomplete hS tgt hunb hWm hW
  exact ⟨φ, hφ, hunbφ, haeφ, fun θ => hopt W' hunb' hWm' hW' θ⟩



/-- Fixture B (weak improvement without completeness): the Rao–Blackwell L² decomposition

alone gives `E(φ(S) − tgt)² ≤ E(W − tgt)²` with no completeness hypothesis. -/

example {Ω Θ τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]

    {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]

    {S : Ω → τ} (hT : Measurable S)

    (hP : MathlibExt.Probability.Statistics.Sufficiency.IsSufficient

      (MeasurableSpace.comap S ‹MeasurableSpace τ›) P)

    {W : Ω → ℝ} (hWm : Measurable W) (hW : ∀ θ, MemLp W 2 (P θ)) (tgt : Θ → ℝ) :

    ∃ φ : τ → ℝ, Measurable φ ∧ ∀ θ,

      ∫ ω, (φ (S ω) - tgt θ) ^ 2 ∂P θ ≤ ∫ ω, (W ω - tgt θ) ^ 2 ∂P θ := by

  obtain ⟨φ, hφ, _, _, hdecomp⟩ :=

    MathlibExt.Probability.Statistics.Sufficiency.raoBlackwell_comap hT hP hWm hW tgt

  refine ⟨φ, hφ, fun θ => ?_⟩

  rw [hdecomp θ]

  have hnn : 0 ≤ ∫ ω, (W ω - φ (S ω)) ^ 2 ∂P θ := by

    apply integral_nonneg_of_ae

    filter_upwards with ω

    exact sq_nonneg _

  linarith



/-- Fixture C (counter-case): a biased competitor can have smaller MSE — the constant

estimator `1/2` beats the sample mean at `p = 1/2`, `n = 1`, so the optimality claim must

quantify over unbiased competitors only. -/

example : ((1 / 2 : ℝ) - 1 / 2) ^ 2 ≤ ((1 : ℝ) - 1 / 2) ^ 2 * (1 / 2) +

    ((0 : ℝ) - 1 / 2) ^ 2 * (1 / 2) := by

  norm_num



end MathlibExtTest.Probability.Statistics.Sufficiency.UMVU

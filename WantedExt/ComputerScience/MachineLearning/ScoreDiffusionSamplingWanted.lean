/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.Generative.ScoreDiffusion
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Sampling is as easy as learning the score: wanted

S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy as learning the
score: theory for diffusion models with minimal data assumptions*, arXiv:2209.11215v3,
Theorem 2 (DDPM) under Assumptions 1-3: if the scores of the forward Ornstein–Uhlenbeck
marginals `q_t` of the data law `q` are `L`-Lipschitz (`L ≥ 1`), `q` has finite second moment
`m₂²`, and the score estimates have mean-square error at most `ε²` at the grid times `k h`,
`k = 1, …, N`, then for a step `h = T / N ≲ 1 / L` the output law `p_T` of the DDPM sampler
started at the standard Gaussian `γ` satisfies
`TV(p_T, q) ≲ √(KL(q ‖ γ)) e^{-T} + (L √(d h) + L m₂ h) √T + ε √T`.

The forward marginals and the sampler are the law-level definitions of
`CSLibExt.MachineLearning.Generative.ScoreDiffusion`. The source's proof uses the time reversal
of the forward process, Girsanov's theorem and the entropy decay of the Ornstein–Uhlenbeck
semigroup; none of this is claimed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ContDiff
open Cslib.MachineLearning.ScoreDiffusion

namespace Cslib.MachineLearning.ScoreDiffusionWanted

/-- **Sampling guarantee for score-based diffusion (DDPM).** There are universal constants
`C, c > 0` such that the following holds. Let `q` be a probability measure on `ℝ^d` whose
forward Ornstein–Uhlenbeck marginals `q_t` have positive differentiable densities `ρ t` (smooth
at `t = 0`) with `L`-Lipschitz scores, `L ≥ 1`, finite second moment `m₂²`, and finite KL
divergence from the standard Gaussian `γ`. Let `T > 0`, `N ≥ 1`, `h = T / N ≤ c / L`, and let
measurable estimates `s k` satisfy `E_{q_{kh}} ‖s k - ∇ log ρ (kh)‖² ≤ ε²` for `k = 1, …, N`.
Then the output law `p_T` of the sampler satisfies
`TV(p_T, q) ≤ C (√(KL(q ‖ γ)) e^{-T} + (L √(d h) + L m₂ h) √T + ε √T)`.

Mathlib's `tvDist` is twice the `sup_A |μ A - ν A|` distance; the factor is absorbed in `C`.

Source: S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, arXiv:2209.11215v3,
Theorem 2 with Assumptions 1-3. Full support and a smooth density of `q` are the standing
assumptions of the source's Section 2; finiteness of the KL divergence is assumption A3 of its
introduction (the bound is vacuous without it); measurability of the estimates is implicit in
the source (it makes `p_T` a law). -/
theorem_wanted tvDist_ddpmOutput_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (d : ℕ) (q : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure q]
      (ρ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
      (s : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (L : ℝ≥0) (T ε : ℝ) (N : ℕ),
      1 ≤ L → 0 < T → 0 < N → T / N ≤ c / L → 0 ≤ ε →
      ContDiff ℝ ∞ (ρ 0) →
      (∀ t, 0 ≤ t → ouMarginal q t = volume.withDensity fun x => ENNReal.ofReal (ρ t x)) →
      (∀ t, 0 ≤ t → ∀ x, 0 < ρ t x) →
      (∀ t, 0 ≤ t → Differentiable ℝ (ρ t)) →
      (∀ t, 0 ≤ t → LipschitzWith L (logDensityScore (ρ t))) →
      ∫⁻ x, ‖x‖ₑ ^ 2 ∂q < ⊤ →
      (∀ k, Measurable (s k)) →
      (∀ k ∈ Finset.Icc 1 N,
        ∫⁻ x, ‖s k x - logDensityScore (ρ (k * (T / N))) x‖ₑ ^ 2 ∂(ouMarginal q (k * (T / N)))
          ≤ ENNReal.ofReal (ε ^ 2)) →
      klDiv q (stdGaussian _) ≠ ⊤ →
      tvDist (ddpmOutput (T / N) s N) q ≤
        C * ((klDiv q (stdGaussian _)).toReal.sqrt * Real.exp (-T) +
          (L * Real.sqrt (d * (T / N)) + L * Real.sqrt (∫ x, ‖x‖ ^ 2 ∂q) * (T / N)) *
            Real.sqrt T +
          ε * Real.sqrt T)

end Cslib.MachineLearning.ScoreDiffusionWanted

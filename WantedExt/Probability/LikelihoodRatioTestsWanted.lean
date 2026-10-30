/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.MLEAsymptoticNormality

/-!
# Local power of the likelihood-ratio test: wishlist

Under local alternatives `θₙ = θ₀ + h / √n`, the likelihood-ratio statistic of a consistent root
of the likelihood equation converges in distribution to the noncentral chi-square law with one
degree of freedom and noncentrality `h² I(θ₀)`, the law of `(Z + h √I(θ₀))²` for a standard
normal `Z`. The standard proof goes through local asymptotic normality at `θ₀`, contiguity of
the alternatives (Le Cam's first lemma) and Le Cam's third lemma, none of which is available in
the pinned Mathlib; the null case `h = 0` is proved in
`MathlibExt.Probability.Statistics.LikelihoodRatioTests`.

The observations form a triangular array: row `n` is i.i.d. with law `p θₙ ν`. The regularity
conditions are the Cramér conditions at `θ₀` used for the null case.

## References

* S. S. Wilks, "The large-sample distribution of the likelihood ratio for testing composite
  hypotheses", Ann. Math. Statist. 9 (1938) 60–62.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), ch. 6 (contiguity, Le Cam's third
  lemma) and ch. 16.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Statistics.FisherInformation
open MathlibExt.Probability.Statistics.MLEAsymptoticNormality

namespace MathlibExt.Probability.Statistics.LikelihoodRatioTestsWanted

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Local power of the likelihood-ratio test.** Let row `n` of the triangular array
`X n 0, X n 1, …` be i.i.d. with law `p θₙ ν`, `θₙ = θ₀ + h / √n`, under the Cramér conditions
at `θ₀` of `LikelihoodRatioTests.tendstoInDistribution_two_mul_logLikelihood_sub`. If `θ̂ₙ`
solves the likelihood equation for row `n` with probability tending to one and `θ̂ₙ → θ₀` in
probability, then `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀))` converges in distribution to the law of
`(Z + h √I(θ₀))²`, `Z ~ N(0, 1)` (noncentral `χ²₁` with noncentrality `h² I(θ₀)`).

Source: van der Vaart (1998), ch. 16 (via Le Cam's third lemma, ch. 6). -/
theorem_wanted tendstoInDistribution_two_mul_logLikelihood_sub_local
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ h : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (Function.uncurry p))
    {X : ℕ → ℕ → Ω → 𝓧}
    (hX_law : ∀ n i, HasLaw (X n i) (lawOf ν p (θ₀ + h / √n)) P)
    (hX_indep : ∀ n, iIndepFun (X n) P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto
      (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X n i ω) ≠ 0}) atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z ((gaussianReal (h * √(fisherInformation ν p θ₀)) 1).map
      (fun x : ℝ => x ^ 2)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (p (θhat n ω) (X n i ω)) - Real.log (p θ₀ (X n i ω))))
      atTop Z (fun _ => P) P'

end MathlibExt.Probability.Statistics.LikelihoodRatioTestsWanted

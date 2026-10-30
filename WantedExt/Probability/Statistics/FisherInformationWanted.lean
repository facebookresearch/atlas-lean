/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fisher information, the Cramér–Rao bound, and consistency of maximum likelihood

A one-parameter statistical model is a family of densities `p θ` (`θ ∈ ℝ`) with respect to a
reference measure `ν` on a sample space `𝓧`. Its **Fisher information** at `θ` is
`I(θ) = ∫ (∂_θ p θ x)² / p θ x dν(x)`, the variance of the score `∂_θ log p θ x`
(`fisherInformation`). The **Cramér–Rao inequality** says that an estimator `T` that is
unbiased for `g θ` on a neighborhood of `θ` has variance at least `g'(θ)² / I(θ)`, provided
differentiation under the integral sign is allowed; the regularity conditions are stated as
explicit hypotheses of `cramerRao`.

**Wald's theorem** (consistency of maximum likelihood) is stated in the form of Ferguson
(1996, Theorem 17) for a compact metric parameter space `Θ`, densities that are positive and
continuous in `θ`, an integrable upper envelope `K` for the log-likelihood ratios, and an
identifiable model: for an i.i.d. sample from `p θ₀`, every sequence of maximizers of the
sample log-likelihood converges to `θ₀` almost surely. Positivity of the densities is assumed
so that `Real.log` needs no junk-value convention; Ferguson's version allows zeros and upper
semicontinuity.

Asymptotic normality of the maximum-likelihood estimator (Cramér 1946) is not stated here.

Sources: H. Cramér, *Mathematical Methods of Statistics* (1946), ch. 32; C. R. Rao,
"Information and the accuracy attainable in the estimation of statistical parameters",
Bull. Calcutta Math. Soc. 37 (1945) 81–91; A. Wald, "Note on the consistency of the maximum
likelihood estimate", Ann. Math. Statist. 20 (1949) 595–601; T. S. Ferguson, *A Course in Large
Sample Theory* (1996), Theorem 17; E. L. Lehmann and G. Casella, *Theory of Point Estimation*,
2nd ed. (1998), ch. 2.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

namespace MathlibExt.Probability.Statistics.FisherInformationWanted

open MeasureTheory ProbabilityTheory Filter Topology

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **Fisher information** at `θ` of the one-parameter family of densities `p θ` with
respect to `ν`: `∫ (∂_θ p θ x)² / p θ x dν(x)`. Points with `p θ x = 0` contribute `0` (for a
nonnegative family differentiable at `θ`, `∂_θ p θ x = 0` there). -/
noncomputable def fisherInformation (ν : Measure 𝓧) (p : ℝ → 𝓧 → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, deriv (fun θ' => p θ' x) θ ^ 2 / p θ x ∂ν

/-- The probability law with density `p θ` with respect to `ν`. -/
noncomputable def lawOf {Θ : Type*} (ν : Measure 𝓧) (p : Θ → 𝓧 → ℝ) (θ : Θ) : Measure 𝓧 :=
  ν.withDensity fun x => ENNReal.ofReal (p θ x)

/-- **Cramér–Rao inequality.** Let `p θ'` be probability densities with respect to `ν` for
`θ'` near `θ`, differentiable in the parameter at `θ`, with finite positive Fisher information
`I(θ)`, and let `T` be an estimator with finite second moment that is unbiased for `g θ'` near
`θ`. If `∫ p θ' dν` and `∫ T p θ' dν` can be differentiated under the integral sign at `θ`,
then `Var_θ T ≥ g'(θ)² / I(θ)`.

Source: Cramér (1946), ch. 32; Rao (1945); Lehmann & Casella (1998), ch. 2. -/
theorem_wanted cramerRao {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {T : 𝓧 → ℝ} {g : ℝ → ℝ} {θ : ℝ}
    (hp_nonneg : ∀ θ' x, 0 ≤ p θ' x)
    (hp_meas : AEStronglyMeasurable (p θ) ν)
    (hp_int : ∀ᶠ θ' in 𝓝 θ, ∫ x, p θ' x ∂ν = 1)
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun θ' => p θ' x) θ)
    (hs_meas : AEStronglyMeasurable (fun x => deriv (fun θ' => p θ' x) θ) ν)
    (hI_int : Integrable (fun x => deriv (fun θ' => p θ' x) θ ^ 2 / p θ x) ν)
    (hI_pos : 0 < fisherInformation ν p θ)
    (hT_meas : AEStronglyMeasurable T ν)
    (hT_sq : Integrable (fun x => T x ^ 2 * p θ x) ν)
    (h_unbiased : ∀ᶠ θ' in 𝓝 θ, ∫ x, T x * p θ' x ∂ν = g θ')
    (h_deriv_one : HasDerivAt (fun θ' => ∫ x, p θ' x ∂ν)
      (∫ x, deriv (fun θ' => p θ' x) θ ∂ν) θ)
    (h_deriv_T : HasDerivAt (fun θ' => ∫ x, T x * p θ' x ∂ν)
      (∫ x, T x * deriv (fun θ' => p θ' x) θ ∂ν) θ) :
    deriv g θ ^ 2 / fisherInformation ν p θ ≤ ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν

/-- **Wald's consistency theorem for maximum likelihood** (Ferguson's form, positive
densities). Let `Θ` be a compact metric space and `p θ` probability densities with respect to
`ν`, positive, measurable in `x` and continuous in `θ`. Assume the model is identifiable
(`p θ = p θ₀` `ν`-a.e. only for `θ = θ₀`) and that the log-likelihood ratios have an upper
envelope `K` integrable under `p θ₀`. Let `X 0, X 1, …` be independent with law `p θ₀ ν`, and
let `θhat n ω` maximize the log-likelihood `∑_{i<n} log p θ (X i ω)` over `θ ∈ Θ`. Then
`θhat n → θ₀` almost surely.

Source: Wald (1949); Ferguson (1996), Theorem 17. -/
theorem_wanted ae_tendsto_maximumLikelihood {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ]
    {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ} {θ₀ : Θ}
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : ∀ θ, Measurable (p θ))
    (hp_cont : ∀ x, Continuous fun θ => p θ x) (hp_int : ∀ θ, ∫ x, p θ x ∂ν = 1)
    (hident : ∀ θ, p θ =ᵐ[ν] p θ₀ → θ = θ₀)
    {K : 𝓧 → ℝ} (hK : Integrable K (lawOf ν p θ₀))
    (hK_bound : ∀ θ x, Real.log (p θ x) - Real.log (p θ₀ x) ≤ K x)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝓧}
    (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    {θhat : ℕ → Ω → Θ}
    (hmle : ∀ n ω θ, ∑ i ∈ Finset.range n, Real.log (p θ (X i ω)) ≤
      ∑ i ∈ Finset.range n, Real.log (p (θhat n ω) (X i ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => θhat n ω) atTop (𝓝 θ₀)

end MathlibExt.Probability.Statistics.FisherInformationWanted

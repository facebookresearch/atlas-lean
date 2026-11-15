/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.EstimatingEquations
public import MathlibExt.Probability.Statistics.InformationInequalityIdentification
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The misspecified maximum-likelihood estimator (White)

`MLEConsistency`, `InformationInequalityIdentification` and `VectorInference` treat the
maximum-likelihood estimator of a **correctly specified** model: the data are drawn from a law
`μ θ₀` of the model, the expected log-likelihood is maximized at `θ₀`, and the limit covariance is
the inverse Fisher information. This file drops correct specification. The observations
`X 0, X 1, …` are IID with an arbitrary law `μ₀`, which need not belong to the model, and the
maximum-likelihood estimator over a compact set `K` is studied as an estimator of the
**pseudo-true value** `θ*`, the maximizer over `K` of the expected log-likelihood
`θ ↦ E_{μ₀} ℓ θ`.

## Results

**The pseudo-true value is the Kullback–Leibler projection.** If `ℓ₀ - ℓ θ` is the
log-likelihood ratio `llr μ₀ (μ θ)` (for densities, `ℓ₀ = log g` with `g` the true density and
`ℓ θ = log p θ`), the expected log-likelihood is `E_{μ₀} ℓ₀ - KL(μ₀ ‖ μ θ)`
(`popCrit_eq_integral_sub_toReal_klDiv`). Hence `θ*` is the unique maximizer of the expected
log-likelihood on `K` exactly when it is the unique minimizer of `θ ↦ KL(μ₀ ‖ μ θ)` on `K`
(`isIdentifiedOn_popCrit_iff_isKLProjectionOn`, density form
`isIdentifiedOn_popCrit_iff_isKLProjectionOn_of_density`).

**Consistency.** Wald's argument (`MLEConsistency.ae_tendsto_of_isMLEOn`) uses only the
population criterion, so with the KL projection in place of the true parameter the misspecified
MLE converges almost surely to the KL projection of the true law onto the model
(`ae_tendsto_of_isMLEOn_of_isKLProjectionOn`).

**Asymptotic normality with the sandwich covariance** (White 1982, Theorem 3.2). Let `θ*` be an
interior point of `K`, let `ℓ · x` have gradient `ψ θ x` near `θ*`, dominated by an integrable
envelope, and let `ψ` satisfy the Cramér conditions of the vector Z-estimator theorem. Then
`√n (θ̂ₙ - θ*) ⇒ N(0, A⁻¹ B A⁻ᵀ)` with `A = E Dψ θ*` and `B = E ψ θ* ψ θ*ᵀ`
(`tendstoInDistribution_sqrt_smul_sub_of_isMLEOn`). The covariance is the repository's sandwich
`GEE.sandwichCovariance A B`, and the limit theorem applied is the merged IID sandwich theorem
`EstimatingEquations.tendstoInDistribution_sqrt_smul_sub_of_clusterEstimatingEquation`. What
this file adds is the derivation, from the maximum-likelihood structure, of the three inputs that
theorem takes as hypotheses:

* the **mean-zero score at the pseudo-true value**, `E ψ θ* = 0`, from the first-order condition
  of the interior maximum of the expected log-likelihood, differentiated under the integral
  (`integral_eq_zero_of_isLocalMax`);
* the **root of the likelihood equation**: an MLE in the interior of `K` solves
  `∑ ψ θ̂ₙ (X i) = 0` (`sum_eq_zero_of_isMLEOn`), so the probability that it does not tends to
  zero (`tendsto_measure_sum_ne_zero_of_isMLEOn`);
* **consistency** of `θ̂ₙ` for `θ*`, from Wald's theorem.

Under misspecification `B ≠ -A` in general, so the sandwich does not reduce to an inverse
information; the tests compute a misspecified model in which the sandwich variance is `4` while
the inverse model information is `1`, and a boundary pseudo-true value at which the expected score
does not vanish.

## References

* H. White, *Maximum likelihood estimation of misspecified models*, Econometrica 50 (1982),
  1–25; Theorems 2.2 and 3.2.
* P. J. Huber, *The behavior of maximum likelihood estimates under nonstandard conditions*,
  Proc. Fifth Berkeley Symp. Math. Statist. Probab. 1 (1967), 221–233.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998; Example 5.25
  and Theorem 5.41.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MisspecifiedMLE

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Metric
open scoped RealInnerProductSpace ENNReal
open MathlibExt.Probability.Statistics.MLEConsistency
open MathlibExt.Probability.Statistics.InformationInequalityIdentification
open MathlibExt.Probability.Statistics.EstimatingEquations

/-! ## The pseudo-true value as the Kullback–Leibler projection -/

section KLProjection

variable {Θ α Ω : Type*} {mα : MeasurableSpace α}

/-- `θstar` is the **Kullback–Leibler projection** of the law `μ₀` onto the model `μ` over `K`:
`θstar ∈ K` and `KL(μ₀ ‖ μ θstar) < KL(μ₀ ‖ μ θ)` for every other `θ ∈ K`. The law `μ₀` need not
belong to the model. -/
def IsKLProjectionOn (K : Set Θ) (μ₀ : Measure α) (μ : Θ → Measure α) (θstar : Θ) : Prop :=
  θstar ∈ K ∧ ∀ θ ∈ K, θ ≠ θstar → klDiv μ₀ (μ θstar) < klDiv μ₀ (μ θ)

variable [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → α} {ℓ : Θ → α → ℝ}
  {μ₀ : Measure α} {μ : Θ → Measure α} {ℓ₀ : α → ℝ}

/-- **The expected log-likelihood of a misspecified model** is `E_{μ₀} ℓ₀ - KL(μ₀ ‖ μ θ)`, where
`μ₀` is the law of `X 0` and `ℓ₀ - ℓ θ = llr μ₀ (μ θ)` `μ₀`-almost everywhere. -/
theorem popCrit_eq_integral_sub_toReal_klDiv [IsProbabilityMeasure μ₀] {θ : Θ}
    [IsProbabilityMeasure (μ θ)] (hX : AEMeasurable (X 0) P) (hlaw : P.map (X 0) = μ₀)
    (hint₀ : Integrable ℓ₀ μ₀) (hint : Integrable (ℓ θ) μ₀) (hac : μ₀ ≪ μ θ)
    (hllr : (fun x => ℓ₀ x - ℓ θ x) =ᵐ[μ₀] llr μ₀ (μ θ)) :
    popCrit P ℓ X θ = ∫ x, ℓ₀ x ∂μ₀ - (klDiv μ₀ (μ θ)).toReal := by
  rw [popCrit_eq_integral hX hlaw hint, ← integral_sub_eq_toReal_klDiv hac hint₀ hint hllr]
  ring

/-- Under the hypotheses of `popCrit_eq_integral_sub_toReal_klDiv` at `θ` and `θ'`, the expected
log-likelihood is larger at `θ'` exactly when `μ θ'` is closer to `μ₀` in Kullback–Leibler
divergence. -/
theorem popCrit_lt_popCrit_iff [IsProbabilityMeasure μ₀] {θ θ' : Θ}
    [IsProbabilityMeasure (μ θ)] [IsProbabilityMeasure (μ θ')]
    (hX : AEMeasurable (X 0) P) (hlaw : P.map (X 0) = μ₀) (hint₀ : Integrable ℓ₀ μ₀)
    (hint : Integrable (ℓ θ) μ₀) (hint' : Integrable (ℓ θ') μ₀) (hac : μ₀ ≪ μ θ)
    (hac' : μ₀ ≪ μ θ') (hllr : (fun x => ℓ₀ x - ℓ θ x) =ᵐ[μ₀] llr μ₀ (μ θ))
    (hllr' : (fun x => ℓ₀ x - ℓ θ' x) =ᵐ[μ₀] llr μ₀ (μ θ')) :
    popCrit P ℓ X θ < popCrit P ℓ X θ' ↔ klDiv μ₀ (μ θ') < klDiv μ₀ (μ θ) := by
  have hne : klDiv μ₀ (μ θ) ≠ ∞ := klDiv_ne_top hac ((hint₀.sub hint).congr hllr)
  have hne' : klDiv μ₀ (μ θ') ≠ ∞ := klDiv_ne_top hac' ((hint₀.sub hint').congr hllr')
  rw [popCrit_eq_integral_sub_toReal_klDiv hX hlaw hint₀ hint hac hllr,
    popCrit_eq_integral_sub_toReal_klDiv hX hlaw hint₀ hint' hac' hllr',
    ← ENNReal.toReal_lt_toReal hne' hne]
  constructor <;> intro h <;> linarith

/-- **The pseudo-true value is the Kullback–Leibler projection** (abstract form; cf. White 1982,
§2). Let `μ₀`, the law of `X 0`, be a probability measure with `ℓ₀` integrable, and for
every `θ ∈ K` let `μ θ` be a probability measure with `μ₀ ≪ μ θ`, `ℓ θ` integrable under `μ₀` and
`ℓ₀ - ℓ θ = llr μ₀ (μ θ)` `μ₀`-a.e. Then `θstar` is the unique maximizer of the expected
log-likelihood on `K` if and only if it is the unique minimizer of `θ ↦ KL(μ₀ ‖ μ θ)` on `K`.
Nothing requires `μ₀` to be a law of the model. -/
theorem isIdentifiedOn_popCrit_iff_isKLProjectionOn [IsProbabilityMeasure μ₀] {K : Set Θ}
    (hprob : ∀ θ ∈ K, IsProbabilityMeasure (μ θ)) (hX : AEMeasurable (X 0) P)
    (hlaw : P.map (X 0) = μ₀) (hint₀ : Integrable ℓ₀ μ₀)
    (hint : ∀ θ ∈ K, Integrable (ℓ θ) μ₀) (hac : ∀ θ ∈ K, μ₀ ≪ μ θ)
    (hllr : ∀ θ ∈ K, (fun x => ℓ₀ x - ℓ θ x) =ᵐ[μ₀] llr μ₀ (μ θ)) {θstar : Θ} :
    IsIdentifiedOn K (popCrit P ℓ X) θstar ↔ IsKLProjectionOn K μ₀ μ θstar := by
  have key : ∀ θ ∈ K, ∀ θ' ∈ K,
      popCrit P ℓ X θ < popCrit P ℓ X θ' ↔ klDiv μ₀ (μ θ') < klDiv μ₀ (μ θ) :=
    fun θ hθ θ' hθ' => by
      have := hprob θ hθ
      have := hprob θ' hθ'
      exact popCrit_lt_popCrit_iff hX hlaw hint₀ (hint θ hθ) (hint θ' hθ') (hac θ hθ)
        (hac θ' hθ') (hllr θ hθ) (hllr θ' hθ')
  constructor
  · rintro ⟨hmem, h⟩
    exact ⟨hmem, fun θ hθ hne => (key θ hθ θstar hmem).1 (h θ hθ hne)⟩
  · rintro ⟨hmem, h⟩
    exact ⟨hmem, fun θ hθ hne => (key θ hθ θstar hmem).2 (h θ hθ hne)⟩

variable {ν : Measure α} {p : Θ → α → ℝ} {g : α → ℝ}

/-- **The log-likelihood ratio of a positive true density against a positive model density** is
`log g - log p θ`, almost everywhere under the true law `ν.withDensity g`. The true density `g`
need not be a density of the model. -/
theorem llr_withDensity_densityModel_ae_eq [SigmaFinite ν] {θ : Θ} (hg : Measurable g)
    (hgpos : ∀ᵐ x ∂ν, 0 < g x) (hmeas : Measurable (p θ)) (hpos : ∀ᵐ x ∂ν, 0 < p θ x) :
    (fun x => Real.log (g x) - logDensity p θ x)
      =ᵐ[ν.withDensity fun x => ENNReal.ofReal (g x)]
      llr (ν.withDensity fun x => ENNReal.ofReal (g x)) (densityModel ν p θ) :=
  llr_densityModel_ae_eq (ν := ν) (p := fun o : Option Θ => o.elim g p) (θ₀ := none)
    (θ := some θ) hg hmeas hgpos hpos

/-- **The pseudo-true value is the Kullback–Leibler projection** (density form). Let the true
law of `X 0` be `ν.withDensity g` with `g` measurable and `ν`-a.e. positive and `log g`
integrable, and for `θ ∈ K` let `densityModel ν p θ` be a probability measure with `p θ`
measurable, `ν`-a.e. positive and `log p θ` integrable under the true law. Then `θstar` uniquely
maximizes the expected log-likelihood `θ ↦ E log p θ (X 0)` on `K` if and only if it uniquely
minimizes `θ ↦ KL(ν.withDensity g ‖ densityModel ν p θ)` on `K`. -/
theorem isIdentifiedOn_popCrit_iff_isKLProjectionOn_of_density [SigmaFinite ν]
    [IsProbabilityMeasure (ν.withDensity fun x => ENNReal.ofReal (g x))] {K : Set Θ}
    (hg : Measurable g) (hgpos : ∀ᵐ x ∂ν, 0 < g x)
    (hprob : ∀ θ ∈ K, IsProbabilityMeasure (densityModel ν p θ))
    (hmeas : ∀ θ ∈ K, Measurable (p θ)) (hpos : ∀ θ ∈ K, ∀ᵐ x ∂ν, 0 < p θ x)
    (hX : AEMeasurable (X 0) P)
    (hlaw : P.map (X 0) = ν.withDensity fun x => ENNReal.ofReal (g x))
    (hint₀ : Integrable (fun x => Real.log (g x)) (ν.withDensity fun x => ENNReal.ofReal (g x)))
    (hint : ∀ θ ∈ K, Integrable (logDensity p θ) (ν.withDensity fun x => ENNReal.ofReal (g x)))
    {θstar : Θ} :
    IsIdentifiedOn K (popCrit P (logDensity p) X) θstar ↔
      IsKLProjectionOn K (ν.withDensity fun x => ENNReal.ofReal (g x)) (densityModel ν p)
        θstar :=
  isIdentifiedOn_popCrit_iff_isKLProjectionOn hprob hX hlaw hint₀ hint
    (fun θ hθ => (withDensity_absolutelyContinuous ν _).trans
      (absolutelyContinuous_densityModel (hmeas θ hθ) (hpos θ hθ)))
    (fun θ hθ => llr_withDensity_densityModel_ae_eq hg hgpos (hmeas θ hθ) (hpos θ hθ))

/-- **Consistency of the misspecified MLE for the Kullback–Leibler projection** (White 1982,
Theorem 2.2). Under the hypotheses of `isIdentifiedOn_popCrit_iff_isKLProjectionOn_of_density`,
on a compact `K` with `θ ↦ log p θ x` continuous on `K` and the uniform LLN, every
maximum-likelihood estimator on `K` converges almost surely to the KL projection `θstar` of the
true law onto the model, whether or not the true law belongs to the model. -/
theorem ae_tendsto_of_isMLEOn_of_isKLProjectionOn [PseudoMetricSpace Θ] [SigmaFinite ν]
    [IsProbabilityMeasure (ν.withDensity fun x => ENNReal.ofReal (g x))] {K : Set Θ}
    (hK : IsCompact K) (hg : Measurable g) (hgpos : ∀ᵐ x ∂ν, 0 < g x)
    (hprob : ∀ θ ∈ K, IsProbabilityMeasure (densityModel ν p θ))
    (hmeas : ∀ θ ∈ K, Measurable (p θ)) (hpos : ∀ θ ∈ K, ∀ᵐ x ∂ν, 0 < p θ x)
    (hX : AEMeasurable (X 0) P)
    (hlaw : P.map (X 0) = ν.withDensity fun x => ENNReal.ofReal (g x))
    (hint₀ : Integrable (fun x => Real.log (g x)) (ν.withDensity fun x => ENNReal.ofReal (g x)))
    (hint : ∀ θ ∈ K, Integrable (logDensity p θ) (ν.withDensity fun x => ENNReal.ofReal (g x)))
    {θstar : Θ}
    (hproj : IsKLProjectionOn K (ν.withDensity fun x => ENNReal.ofReal (g x)) (densityModel ν p)
      θstar)
    (hcont : ∀ x, ContinuousOn (fun θ => logDensity p θ x) K)
    (hULLN : UniformLLNOn P K (logDensity p) X) {est : ℕ → Ω → Θ}
    (hest : IsMLEOn K (logDensity p) X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θstar) :=
  ae_tendsto_of_isMLEOn hK hcont
    ((isIdentifiedOn_popCrit_iff_isKLProjectionOn_of_density hg hgpos hprob hmeas hpos hX hlaw
      hint₀ hint).2 hproj) hULLN hest

end KLProjection

/-! ## The first-order condition at the pseudo-true value -/

section FirstOrder

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The expected score vanishes at an interior maximum of the expected log-likelihood.** If
`θ₀` is a local maximum of `θ ↦ ∫ ℓ θ dμ`, and on the ball of radius `δ > 0` about `θ₀` the
function `ℓ · x` has gradient `ψ θ x` with `‖ψ θ x‖ ≤ G x` for an integrable `G`, `ℓ θ` is
a.e. strongly measurable and `ℓ θ₀` integrable, then `∫ ψ θ₀ dμ = 0`. No model is involved: under
misspecification this is the estimating equation `E ψ θ* = 0` satisfied by the pseudo-true value. -/
theorem integral_eq_zero_of_isLocalMax {μ : Measure 𝓧} {ℓ : E → 𝓧 → ℝ} {ψ : E → 𝓧 → E}
    {θ₀ : E} {δ : ℝ} (hδ : 0 < δ) (hmax : IsLocalMax (fun θ => ∫ x, ℓ θ x ∂μ) θ₀)
    (hgrad : ∀ x, ∀ θ ∈ ball θ₀ δ, HasGradientAt (fun t => ℓ t x) (ψ θ x) θ)
    (hℓ_meas : ∀ θ ∈ ball θ₀ δ, AEStronglyMeasurable (ℓ θ) μ) (hℓ_int : Integrable (ℓ θ₀) μ)
    (hψ_meas : AEStronglyMeasurable (ψ θ₀) μ) {G : 𝓧 → ℝ} (hG_int : Integrable G μ)
    (hG : ∀ x, ∀ θ ∈ ball θ₀ δ, ‖ψ θ x‖ ≤ G x) :
    ∫ x, ψ θ₀ x ∂μ = 0 := by
  have hball : ball θ₀ δ ∈ 𝓝 θ₀ := ball_mem_nhds θ₀ hδ
  have hD_meas : AEStronglyMeasurable (fun x => InnerProductSpace.toDual ℝ E (ψ θ₀ x)) μ :=
    (InnerProductSpace.toDual ℝ E).continuous.comp_aestronglyMeasurable hψ_meas
  have hD_int : Integrable (fun x => InnerProductSpace.toDual ℝ E (ψ θ₀ x)) μ :=
    hG_int.mono' hD_meas (ae_of_all _ fun x => by
      rw [LinearIsometryEquiv.norm_map]
      exact hG x θ₀ (mem_ball_self hδ))
  have hψ_int : Integrable (ψ θ₀) μ :=
    hG_int.mono' hψ_meas (ae_of_all _ fun x => hG x θ₀ (mem_ball_self hδ))
  have hderiv : HasFDerivAt (fun θ => ∫ x, ℓ θ x ∂μ)
      (∫ x, InnerProductSpace.toDual ℝ E (ψ θ₀ x) ∂μ) θ₀ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun θ x => InnerProductSpace.toDual ℝ E (ψ θ x)) hball
      (eventually_of_mem hball hℓ_meas) hℓ_int hD_meas
      (ae_of_all _ fun x θ hθ => by
        rw [LinearIsometryEquiv.norm_map]
        exact hG x θ hθ)
      hG_int (ae_of_all _ fun x θ hθ => (hgrad x θ hθ).hasFDerivAt)
  have h0 := hmax.hasFDerivAt_eq_zero hderiv
  set v := ∫ x, ψ θ₀ x ∂μ
  have h1 : ∫ x, ⟪ψ θ₀ x, v⟫ ∂μ = 0 := by
    have h := congrArg (fun L : StrongDual ℝ E => L v) h0
    simpa only [ContinuousLinearMap.integral_apply hD_int, _root_.zero_apply,
      InnerProductSpace.toDual_apply_apply] using h
  have h2 : ∫ x, ⟪v, ψ θ₀ x⟫ ∂μ = 0 := by
    rw [← h1]
    exact integral_congr_ae (ae_of_all _ fun x => real_inner_comm _ _)
  rw [integral_inner hψ_int, inner_self_eq_zero] at h2
  exact h2

end FirstOrder

/-! ## Roots of the likelihood equation -/

section Root

variable {𝓧 : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Ω : Type*}

/-- **An interior maximum-likelihood estimate solves the likelihood equation.** If `est` is an
MLE on `K`, `K` is a neighbourhood of `est n ω`, and every `ℓ · (X i ω)`, `i < n`, has gradient
`ψ (est n ω) (X i ω)` at `est n ω`, then `∑_{i<n} ψ (est n ω) (X i ω) = 0`. -/
theorem sum_eq_zero_of_isMLEOn {K : Set E} {ℓ : E → 𝓧 → ℝ} {X : ℕ → Ω → 𝓧} {est : ℕ → Ω → E}
    (hest : IsMLEOn K ℓ X est) {ψ : E → 𝓧 → E} {n : ℕ} {ω : Ω} (hK : K ∈ 𝓝 (est n ω))
    (hgrad : ∀ i ∈ Finset.range n,
      HasGradientAt (fun t => ℓ t (X i ω)) (ψ (est n ω) (X i ω)) (est n ω)) :
    ∑ i ∈ Finset.range n, ψ (est n ω) (X i ω) = 0 := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  have hmax : IsLocalMax (avgLogLik ℓ X n ω) (est n ω) :=
    eventually_of_mem hK fun θ hθ => (hest n ω).2 θ hθ
  have hderiv : HasFDerivAt (avgLogLik ℓ X n ω)
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
        InnerProductSpace.toDual ℝ E (ψ (est n ω) (X i ω))) (est n ω) :=
    (HasFDerivAt.fun_sum fun i hi => (hgrad i hi).hasFDerivAt).const_mul ((n : ℝ)⁻¹)
  have h0 := hmax.hasFDerivAt_eq_zero hderiv
  set v := ∑ i ∈ Finset.range n, ψ (est n ω) (X i ω)
  have h1 := congrArg (fun L : StrongDual ℝ E => L v) h0
  simp only [_root_.smul_apply, _root_.zero_apply, smul_eq_mul] at h1
  rw [FunLike.coe_sum, Finset.sum_apply] at h1
  simp only [InnerProductSpace.toDual_apply_apply] at h1
  rw [← sum_inner] at h1
  have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hn.ne')
  exact inner_self_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hn')

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- **The MLE solves the likelihood equation with probability tending to one.** If `est` is an
MLE on `K` that converges in probability to an interior point `θstar` of `K`, and `ℓ · x` has
gradient `ψ θ x` at every `θ` of a ball about `θstar`, then the probability that
`∑_{i<n} ψ (est n) (X i) ≠ 0` tends to zero. -/
theorem tendsto_measure_sum_ne_zero_of_isMLEOn {K : Set E} {ℓ : E → 𝓧 → ℝ} {X : ℕ → Ω → 𝓧}
    {est : ℕ → Ω → E} (hest : IsMLEOn K ℓ X est) {θstar : E} (hθ_int : θstar ∈ interior K)
    {ψ : E → 𝓧 → E} {δ : ℝ} (hδ : 0 < δ)
    (hgrad : ∀ x, ∀ θ ∈ ball θstar δ, HasGradientAt (fun t => ℓ t x) (ψ θ x) θ)
    (hcons : TendstoInMeasure P est atTop fun _ => θstar) :
    Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, ψ (est n ω) (X i ω) ≠ 0}) atTop (𝓝 0) := by
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hθ_int)
  have hρ : 0 < min r δ := lt_min hr hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hcons (ENNReal.ofReal (min r δ)) (ENNReal.ofReal_pos.2 hρ)) (fun _ => zero_le)
    (fun n => measure_mono fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt
  rw [not_le, edist_lt_ofReal] at hlt
  have hmem : est n ω ∈ ball θstar (min r δ) := hlt
  refine hω (sum_eq_zero_of_isMLEOn hest ?_ fun i _ =>
    hgrad _ _ (ball_subset_ball (min_le_right _ _) hmem))
  exact mem_of_superset (isOpen_ball.mem_nhds hmem)
    ((ball_subset_ball (min_le_left _ _)).trans hrK)

end Root

/-! ## Asymptotic normality with the sandwich covariance -/

/-- **Asymptotic normality of the misspecified MLE** (White 1982, Theorem 3.2). Let
`X 0, X 1, …` be IID with an arbitrary law `μX` (not assumed to belong to any model), `ℓ θ x` a
log-likelihood, and `est` a maximum-likelihood estimator on a compact `K ⊆ E`, a.e. strongly
measurable. Assume:

* **Wald conditions**: `θ ↦ ℓ θ x` continuous on `K`, the uniform LLN on `K`, and a unique
  maximizer `θstar` of the expected log-likelihood on `K` (the pseudo-true value, equivalently the
  Kullback–Leibler projection, `isIdentifiedOn_popCrit_iff_isKLProjectionOn`), lying in the
  **interior** of `K`;
* **score**: on the ball of radius `δ > 0` about `θstar`, `ℓ · x` has gradient `ψ θ x`, with
  `‖ψ θ x‖ ≤ G x` for an integrable `G`, `ℓ θ` a.e. strongly measurable and `ℓ θstar` integrable;
* **Cramér conditions** on `ψ` as in the vector Z-estimator theorem, and a nonsingular
  `A = E Dψ θstar`.

Then `√n (est n - θstar) ⇒ Z` for every `Z` with `⟪Z, t⟫ ~ N(0, ⟪A⁻¹ B A⁻ᵀ t, t⟫)`, where
`A⁻¹ B A⁻ᵀ = GEE.sandwichCovariance A B` and `B = covarianceOperator (μX.map (ψ θstar))`. The
estimating equation `E ψ θstar = 0`, the root of the likelihood equation and the consistency of
`est` are derived, not assumed. -/
theorem tendstoInDistribution_sqrt_smul_sub_of_isMLEOn
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {μX : Measure 𝓧} {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) μX P)
    (hX_indep : iIndepFun X P)
    {ℓ : E → 𝓧 → ℝ} {K : Set E} (hK : IsCompact K)
    (hcont : ∀ x, ContinuousOn (fun θ => ℓ θ x) K) (hULLN : UniformLLNOn P K ℓ X)
    {θstar : E} (hId : IsIdentifiedOn K (popCrit P ℓ X) θstar) (hθ_int : θstar ∈ interior K)
    {est : ℕ → Ω → E} (hest : IsMLEOn K ℓ X est)
    (hest_meas : ∀ n, AEStronglyMeasurable (est n) P)
    {ψ : E → 𝓧 → E} {δ : ℝ} (hδ : 0 < δ)
    (hgrad : ∀ x, ∀ θ ∈ ball θstar δ, HasGradientAt (fun t => ℓ t x) (ψ θ x) θ)
    (hℓ_meas : ∀ θ ∈ ball θstar δ, AEStronglyMeasurable (ℓ θ) μX)
    (hℓ_int : Integrable (ℓ θstar) μX)
    {G : 𝓧 → ℝ} (hG_int : Integrable G μX) (hG : ∀ x, ∀ θ ∈ ball θstar δ, ‖ψ θ x‖ ≤ G x)
    (hψ_diff : ∀ x, ∀ θ ∈ ball θstar δ, DifferentiableAt ℝ (fun t => ψ t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M μX)
    (hM : ∀ x, ∀ θ ∈ ball θstar δ,
      ‖fderiv ℝ (fun t => ψ t x) θ - fderiv ℝ (fun t => ψ t x) θstar‖ ≤ M x * ‖θ - θstar‖)
    (hψ_meas : Measurable (ψ θstar)) (hψ_sq : Integrable (fun x => ‖ψ θstar x‖ ^ 2) μX)
    (hψ'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => ψ t x) θstar)
    (hψ'_int : Integrable (fun x => fderiv ℝ (fun t => ψ t x) θstar) μX)
    (hA : IsUnit (∫ x, fderiv ℝ (fun t => ψ t x) θstar ∂μX))
    {Z : Ω' → E} (hZ_meas : AEMeasurable Z P')
    (hZ : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0
        (⟪GEE.sandwichCovariance (∫ x, fderiv ℝ (fun t => ψ t x) θstar ∂μX)
          (covarianceOperator (μX.map (ψ θstar))) t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (est n ω - θstar)) atTop Z
      (fun _ => P) P' := by
  have hcons : TendstoInMeasure P est atTop fun _ => θstar :=
    tendstoInMeasure_of_isMLEOn hK hcont hId hULLN hest hest_meas
  have hroot := tendsto_measure_sum_ne_zero_of_isMLEOn hest hθ_int hδ hgrad hcons
  have hmean : ∫ x, ψ θstar x ∂μX = 0 := by
    have hmax : IsLocalMax (popCrit P ℓ X) θstar :=
      eventually_of_mem (mem_interior_iff_mem_nhds.1 hθ_int) fun θ hθ => by
        rcases eq_or_ne θ θstar with rfl | hne
        · exact le_rfl
        · exact (hId.2 θ hθ hne).le
    have heq : popCrit P ℓ X =ᶠ[𝓝 θstar] fun θ => ∫ x, ℓ θ x ∂μX :=
      eventually_of_mem (ball_mem_nhds θstar hδ) fun θ hθ =>
        (hX_law 0).integral_comp (hℓ_meas θ hθ)
    exact integral_eq_zero_of_isLocalMax hδ (hmax.congr heq) hgrad hℓ_meas hℓ_int
      hψ_meas.aestronglyMeasurable hG_int hG
  exact tendstoInDistribution_sqrt_smul_sub_of_clusterEstimatingEquation hX_law hX_indep hδ
    hψ_diff hM_meas hM_int hM hψ_meas hψ_sq hmean hψ'_meas hψ'_int hA
    (fun n => (hest_meas n).aemeasurable) hroot hcons hZ_meas hZ

end MathlibExt.Probability.Statistics.MisspecifiedMLE

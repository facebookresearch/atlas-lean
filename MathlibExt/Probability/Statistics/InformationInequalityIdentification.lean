/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import MathlibExt.Probability.Statistics.MLEConsistency

/-!
# Identifiability of the population criterion from the information inequality

`MLEConsistency` proves Wald consistency of the maximum-likelihood estimator under the
unique-maximizer condition `IsIdentifiedOn K (popCrit P ℓ X) θ₀`: the expected log-likelihood
`θ ↦ ∫ ℓ θ (X 0) dP` has the unique maximizer `θ₀` on `K`. This file derives that condition, for
a correctly specified model, from **identifiability of the law** (`θ ↦ P_θ` injective on `K`
at `θ₀`) via the **information inequality**: the gap of the population criterion is a
Kullback–Leibler divergence,

  `popCrit θ₀ - popCrit θ = KL(P_θ₀ ‖ P_θ)`,

which is nonnegative (Gibbs' inequality) and vanishes only when `P_θ = P_θ₀` (Mathlib's
`InformationTheory.klDiv_eq_zero_iff`).

## Setting

* **Abstract form.** `μ : Θ → Measure α` is the model, the law of one observation `X 0` under
  `P` is `μ θ₀` (correct specification), and the log-likelihood `ℓ` satisfies, for `θ ∈ K`,
  `μ θ₀ ≪ μ θ` and `ℓ θ₀ - ℓ θ = llr (μ θ₀) (μ θ)` `μ θ₀`-almost everywhere, with `ℓ θ`
  integrable under `μ θ₀`. No density is mentioned.
* **Density form.** `μ θ = ν.withDensity (ofReal ∘ p θ)` for a σ-finite reference measure `ν`
  (`densityModel ν p θ`), with `p θ` measurable and `ν`-a.e. positive, and `ℓ θ = log ∘ p θ`
  (`logDensity p`). The log-likelihood-ratio and absolute-continuity conditions of the
  abstract form are derived from these.

The positivity of the densities on `K` is used: with a real-valued log-likelihood a density
that vanishes on a set of positive `μ θ₀`-mass has `log 0 = 0` there, and the information
inequality fails (see the tests).

## Main results

* `integral_sub_eq_toReal_klDiv`: `∫ f dμ - ∫ g dμ = KL(μ ‖ ν)` when `f - g = llr μ ν`.
* `integral_le_of_llr`, `integral_lt_of_llr`: the information inequality and its strict form
  for `μ ≠ ν`.
* `popCrit_sub_popCrit_eq_toReal_klDiv`: the gap of the population criterion is
  `KL(μ θ₀ ‖ μ θ)`.
* `isIdentifiedOn_popCrit_of_llr`: identifiability of the law implies `IsIdentifiedOn`
  (abstract form).
* `llr_densityModel_ae_eq`: for positive densities, `llr (P_θ₀) (P_θ) = log p θ₀ - log p θ`.
* `isIdentifiedOn_popCrit_of_densityModel`, `isIdentifiedOn_popCrit_of_densityModel_of_ae_eq`:
  identifiability of the law, or of the density up to `ν`-null sets, implies `IsIdentifiedOn`
  for the log-density criterion.
* `ae_tendsto_of_isMLEOn_of_densityModel`: Wald consistency of the MLE (`MLEConsistency`'s
  `ae_tendsto_of_isMLEOn`) with identifiability of the law in place of `IsIdentifiedOn`.

## References

* A. Wald, *Note on the consistency of the maximum likelihood estimate*, Annals of Mathematical
  Statistics 20 (1949), 595–601 (Lemma 1).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998; Lemma 5.35
  (p. 62).
* W. K. Newey and D. McFadden, *Large sample estimation and hypothesis testing*, Handbook of
  Econometrics, vol. 4, ch. 36, 1994; Lemma 2.2 (p. 2124).
-/

@[expose] public section

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.InformationInequalityIdentification

open MathlibExt.Probability.Statistics.MLEConsistency

variable {Θ α Ω : Type*} {mα : MeasurableSpace α}

/-! ## The information inequality for log-likelihood differences -/

section Gibbs

variable {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f g : α → ℝ}

/-- If `f - g` is the log-likelihood ratio `llr μ ν` `μ`-almost everywhere, the difference of
the `μ`-integrals of `f` and `g` is the Kullback–Leibler divergence `KL(μ ‖ ν)`. -/
theorem integral_sub_eq_toReal_klDiv (hac : μ ≪ ν) (hf : Integrable f μ) (hg : Integrable g μ)
    (hllr : (fun x => f x - g x) =ᵐ[μ] llr μ ν) :
    ∫ x, f x ∂μ - ∫ x, g x ∂μ = (klDiv μ ν).toReal := by
  rw [← integral_sub hf hg, integral_congr_ae hllr,
    toReal_klDiv_of_measure_eq hac (by simp only [measure_univ])]

/-- **The information inequality**: if `f - g = llr μ ν` `μ`-almost everywhere then
`∫ g dμ ≤ ∫ f dμ`. -/
theorem integral_le_of_llr (hac : μ ≪ ν) (hf : Integrable f μ) (hg : Integrable g μ)
    (hllr : (fun x => f x - g x) =ᵐ[μ] llr μ ν) : ∫ x, g x ∂μ ≤ ∫ x, f x ∂μ := by
  have h := integral_sub_eq_toReal_klDiv hac hf hg hllr
  linarith [ENNReal.toReal_nonneg (a := klDiv μ ν)]

/-- **The strict information inequality**: if `f - g = llr μ ν` `μ`-almost everywhere and
`μ ≠ ν` then `∫ g dμ < ∫ f dμ`. -/
theorem integral_lt_of_llr (hac : μ ≪ ν) (hf : Integrable f μ) (hg : Integrable g μ)
    (hllr : (fun x => f x - g x) =ᵐ[μ] llr μ ν) (hne : μ ≠ ν) :
    ∫ x, g x ∂μ < ∫ x, f x ∂μ := by
  have hint : Integrable (llr μ ν) μ := (hf.sub hg).congr hllr
  have h0 : klDiv μ ν ≠ 0 := fun h => hne (klDiv_eq_zero_iff.1 h)
  have hpos : 0 < (klDiv μ ν).toReal := ENNReal.toReal_pos h0 (klDiv_ne_top hac hint)
  have h := integral_sub_eq_toReal_klDiv hac hf hg hllr
  linarith

end Gibbs

/-! ## The population criterion of a correctly specified model -/

section PopCrit

variable [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → α} {ℓ : Θ → α → ℝ}

/-- Under correct specification (the law of `X 0` under `P` is `μ₀`), the population criterion
is the `μ₀`-integral of the log-likelihood. -/
theorem popCrit_eq_integral {μ₀ : Measure α} (hX : AEMeasurable (X 0) P)
    (hlaw : P.map (X 0) = μ₀) {θ : Θ} (hint : Integrable (ℓ θ) μ₀) :
    popCrit P ℓ X θ = ∫ x, ℓ θ x ∂μ₀ := by
  subst hlaw
  exact (integral_map hX hint.aestronglyMeasurable).symm

variable {μ : Θ → Measure α} {θ₀ θ : Θ}

/-- **The gap of the population criterion is a Kullback–Leibler divergence**: under correct
specification at `θ₀`, if `ℓ θ₀ - ℓ θ = llr (μ θ₀) (μ θ)` `μ θ₀`-a.e., then
`popCrit θ₀ - popCrit θ = KL(μ θ₀ ‖ μ θ)`. -/
theorem popCrit_sub_popCrit_eq_toReal_klDiv [IsProbabilityMeasure (μ θ₀)]
    [IsProbabilityMeasure (μ θ)] (hX : AEMeasurable (X 0) P) (hlaw : P.map (X 0) = μ θ₀)
    (hint₀ : Integrable (ℓ θ₀) (μ θ₀)) (hint : Integrable (ℓ θ) (μ θ₀)) (hac : μ θ₀ ≪ μ θ)
    (hllr : (fun x => ℓ θ₀ x - ℓ θ x) =ᵐ[μ θ₀] llr (μ θ₀) (μ θ)) :
    popCrit P ℓ X θ₀ - popCrit P ℓ X θ = (klDiv (μ θ₀) (μ θ)).toReal := by
  rw [popCrit_eq_integral hX hlaw hint₀, popCrit_eq_integral hX hlaw hint]
  exact integral_sub_eq_toReal_klDiv hac hint₀ hint hllr

/-- **Identifiability of the population criterion from identifiability of the law**
(abstract form). Let the law of `X 0` under `P` be `μ θ₀` with `θ₀ ∈ K`, and for every
`θ ∈ K` let `μ θ` be a probability measure with `μ θ₀ ≪ μ θ`, `ℓ θ` be `μ θ₀`-integrable, and
`ℓ θ₀ - ℓ θ = llr (μ θ₀) (μ θ)` `μ θ₀`-a.e. If `μ θ = μ θ₀` with `θ ∈ K` forces `θ = θ₀`, then
`θ₀` is the unique maximizer of the population criterion on `K`. -/
theorem isIdentifiedOn_popCrit_of_llr {K : Set Θ} (hθ₀ : θ₀ ∈ K)
    (hprob : ∀ θ ∈ K, IsProbabilityMeasure (μ θ)) (hX : AEMeasurable (X 0) P)
    (hlaw : P.map (X 0) = μ θ₀) (hint : ∀ θ ∈ K, Integrable (ℓ θ) (μ θ₀))
    (hac : ∀ θ ∈ K, μ θ₀ ≪ μ θ)
    (hllr : ∀ θ ∈ K, (fun x => ℓ θ₀ x - ℓ θ x) =ᵐ[μ θ₀] llr (μ θ₀) (μ θ))
    (hident : ∀ θ ∈ K, μ θ = μ θ₀ → θ = θ₀) :
    IsIdentifiedOn K (popCrit P ℓ X) θ₀ := by
  refine ⟨hθ₀, fun θ hθ hne => ?_⟩
  have := hprob θ₀ hθ₀
  have := hprob θ hθ
  rw [popCrit_eq_integral hX hlaw (hint θ hθ), popCrit_eq_integral hX hlaw (hint θ₀ hθ₀)]
  exact integral_lt_of_llr (hac θ hθ) (hint θ₀ hθ₀) (hint θ hθ) (hllr θ hθ)
    fun h => hne (hident θ hθ h.symm)

end PopCrit

/-! ## Models given by densities -/

section Density

/-- The model with real densities `p θ` with respect to the reference measure `ν`:
`ν.withDensity (fun x => ENNReal.ofReal (p θ x))`. -/
noncomputable def densityModel (ν : Measure α) (p : Θ → α → ℝ) (θ : Θ) : Measure α :=
  ν.withDensity fun x => ENNReal.ofReal (p θ x)

/-- The log-likelihood of the density model: `log (p θ x)`. -/
noncomputable def logDensity (p : Θ → α → ℝ) (θ : Θ) (x : α) : ℝ := Real.log (p θ x)

variable {ν : Measure α} {p : Θ → α → ℝ}

/-- A density model with `ν`-a.e. positive density and `ν` are mutually absolutely continuous;
this is the direction `ν ≪ densityModel ν p θ`. -/
theorem absolutelyContinuous_densityModel {θ : Θ} (hmeas : Measurable (p θ))
    (hpos : ∀ᵐ x ∂ν, 0 < p θ x) : ν ≪ densityModel ν p θ :=
  withDensity_absolutelyContinuous' hmeas.ennreal_ofReal.aemeasurable
    (hpos.mono fun _ hx => ENNReal.ofReal_ne_zero_iff.2 hx)

/-- **The log-likelihood ratio of two positive densities** is the difference of the
log-densities: `llr (P_θ₀) (P_θ) = log p θ₀ - log p θ`, `ν`-almost everywhere. -/
theorem llr_densityModel_ae_eq_of_ae [SigmaFinite ν] {θ₀ θ : Θ} (hmeas₀ : Measurable (p θ₀))
    (hmeas : Measurable (p θ)) (hpos₀ : ∀ᵐ x ∂ν, 0 < p θ₀ x) (hpos : ∀ᵐ x ∂ν, 0 < p θ x) :
    llr (densityModel ν p θ₀) (densityModel ν p θ)
      =ᵐ[ν] fun x => logDensity p θ₀ x - logDensity p θ x := by
  set f₀ : α → ℝ≥0∞ := fun x => ENNReal.ofReal (p θ₀ x)
  set f : α → ℝ≥0∞ := fun x => ENNReal.ofReal (p θ x)
  have hf : Measurable f := hmeas.ennreal_ofReal
  have hf₀ : Measurable f₀ := hmeas₀.ennreal_ofReal
  have hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0 := hpos.mono fun _ hx => ENNReal.ofReal_ne_zero_iff.2 hx
  have hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞ := ae_of_all _ fun _ => ENNReal.ofReal_ne_top
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  have h1 : (ν.withDensity f₀).rnDeriv (ν.withDensity f)
      =ᵐ[ν] fun x => f₀ x * ν.rnDeriv (ν.withDensity f) x :=
    (absolutelyContinuous_densityModel hmeas hpos).ae_eq
      (Measure.rnDeriv_withDensity_left (μ := ν) (ν := ν.withDensity f) hf₀.aemeasurable
        (ae_of_all _ fun _ => ENNReal.ofReal_ne_top))
  have h2 : ν.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x => (f x)⁻¹ * ν.rnDeriv ν x :=
    Measure.rnDeriv_withDensity_right ν ν hf.aemeasurable hf_ne_zero hf_ne_top
  filter_upwards [h1, h2, Measure.rnDeriv_self ν, hpos₀, hpos] with x hx1 hx2 hx3 hx4 hx5
  change Real.log ((ν.withDensity f₀).rnDeriv (ν.withDensity f) x).toReal
    = Real.log (p θ₀ x) - Real.log (p θ x)
  rw [hx1, hx2, hx3, mul_one, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hx4.le, ENNReal.toReal_ofReal hx5.le,
    ← div_eq_mul_inv, Real.log_div hx4.ne' hx5.ne']

/-- `llr_densityModel_ae_eq_of_ae`, `densityModel ν p θ₀`-almost everywhere. -/
theorem llr_densityModel_ae_eq [SigmaFinite ν] {θ₀ θ : Θ} (hmeas₀ : Measurable (p θ₀))
    (hmeas : Measurable (p θ)) (hpos₀ : ∀ᵐ x ∂ν, 0 < p θ₀ x) (hpos : ∀ᵐ x ∂ν, 0 < p θ x) :
    (fun x => logDensity p θ₀ x - logDensity p θ x)
      =ᵐ[densityModel ν p θ₀] llr (densityModel ν p θ₀) (densityModel ν p θ) :=
  (withDensity_absolutelyContinuous ν _).ae_eq
    (llr_densityModel_ae_eq_of_ae hmeas₀ hmeas hpos₀ hpos).symm

/-- Two density models with `ν`-a.e. positive densities are mutually absolutely continuous;
this is the direction `densityModel ν p θ₀ ≪ densityModel ν p θ`. -/
theorem densityModel_absolutelyContinuous {θ₀ θ : Θ} (hmeas : Measurable (p θ))
    (hpos : ∀ᵐ x ∂ν, 0 < p θ x) : densityModel ν p θ₀ ≪ densityModel ν p θ :=
  (withDensity_absolutelyContinuous ν _).trans (absolutelyContinuous_densityModel hmeas hpos)

variable [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → α}

/-- **Identifiability of the population criterion for a density model.** Let `ν` be σ-finite,
`θ₀ ∈ K`, and for `θ ∈ K` let `densityModel ν p θ` be a probability measure with `p θ`
measurable and `ν`-a.e. positive. If the law of `X 0` under `P` is `densityModel ν p θ₀`, the
log-density `log ∘ p θ` is integrable under it for `θ ∈ K`, and the law is identified on `K`
(`densityModel ν p θ = densityModel ν p θ₀`, `θ ∈ K` forces `θ = θ₀`), then `θ₀` is the unique
maximizer of the expected log-likelihood on `K`. -/
theorem isIdentifiedOn_popCrit_of_densityModel [SigmaFinite ν] {K : Set Θ} {θ₀ : Θ}
    (hθ₀ : θ₀ ∈ K) (hprob : ∀ θ ∈ K, IsProbabilityMeasure (densityModel ν p θ))
    (hmeas : ∀ θ ∈ K, Measurable (p θ)) (hpos : ∀ θ ∈ K, ∀ᵐ x ∂ν, 0 < p θ x)
    (hX : AEMeasurable (X 0) P) (hlaw : P.map (X 0) = densityModel ν p θ₀)
    (hint : ∀ θ ∈ K, Integrable (logDensity p θ) (densityModel ν p θ₀))
    (hident : ∀ θ ∈ K, densityModel ν p θ = densityModel ν p θ₀ → θ = θ₀) :
    IsIdentifiedOn K (popCrit P (logDensity p) X) θ₀ :=
  isIdentifiedOn_popCrit_of_llr hθ₀ hprob hX hlaw hint
    (fun θ hθ => densityModel_absolutelyContinuous (hmeas θ hθ) (hpos θ hθ))
    (fun θ hθ => llr_densityModel_ae_eq (hmeas θ₀ hθ₀) (hmeas θ hθ) (hpos θ₀ hθ₀) (hpos θ hθ))
    hident

/-- Equal density models with `ν`-a.e. positive densities have `ν`-a.e. equal densities. -/
theorem ae_eq_of_densityModel_eq [SigmaFinite ν] {θ₀ θ : Θ} (hmeas₀ : Measurable (p θ₀))
    (hmeas : Measurable (p θ)) (hpos₀ : ∀ᵐ x ∂ν, 0 < p θ₀ x) (hpos : ∀ᵐ x ∂ν, 0 < p θ x)
    (h : densityModel ν p θ = densityModel ν p θ₀) : p θ =ᵐ[ν] p θ₀ := by
  have h' := (withDensity_eq_iff_of_sigmaFinite hmeas.ennreal_ofReal.aemeasurable
    hmeas₀.ennreal_ofReal.aemeasurable).1 h
  filter_upwards [h', hpos₀, hpos] with x hx h0 h1
  exact (ENNReal.ofReal_eq_ofReal_iff h1.le h0.le).1 hx

/-- `isIdentifiedOn_popCrit_of_densityModel` with identifiability of the density up to
`ν`-null sets: `p θ =ᵐ[ν] p θ₀` with `θ ∈ K` forces `θ = θ₀`. -/
theorem isIdentifiedOn_popCrit_of_densityModel_of_ae_eq [SigmaFinite ν] {K : Set Θ} {θ₀ : Θ}
    (hθ₀ : θ₀ ∈ K) (hprob : ∀ θ ∈ K, IsProbabilityMeasure (densityModel ν p θ))
    (hmeas : ∀ θ ∈ K, Measurable (p θ)) (hpos : ∀ θ ∈ K, ∀ᵐ x ∂ν, 0 < p θ x)
    (hX : AEMeasurable (X 0) P) (hlaw : P.map (X 0) = densityModel ν p θ₀)
    (hint : ∀ θ ∈ K, Integrable (logDensity p θ) (densityModel ν p θ₀))
    (hident : ∀ θ ∈ K, p θ =ᵐ[ν] p θ₀ → θ = θ₀) :
    IsIdentifiedOn K (popCrit P (logDensity p) X) θ₀ :=
  isIdentifiedOn_popCrit_of_densityModel hθ₀ hprob hmeas hpos hX hlaw hint fun θ hθ h =>
    hident θ hθ (ae_eq_of_densityModel_eq (hmeas θ₀ hθ₀) (hmeas θ hθ) (hpos θ₀ hθ₀)
      (hpos θ hθ) h)

/-- **Wald consistency of the MLE with identifiability of the law.** `MLEConsistency`'s
`ae_tendsto_of_isMLEOn` with the unique-maximizer hypothesis replaced by the hypotheses of
`isIdentifiedOn_popCrit_of_densityModel`: for a correctly specified density model on a compact
`K`, with `θ ↦ log p θ x` continuous on `K` and the uniform LLN, every maximum-likelihood
estimator converges to `θ₀` almost surely. -/
theorem ae_tendsto_of_isMLEOn_of_densityModel [PseudoMetricSpace Θ] [SigmaFinite ν]
    {K : Set Θ} (hK : IsCompact K) {θ₀ : Θ} (hθ₀ : θ₀ ∈ K)
    (hprob : ∀ θ ∈ K, IsProbabilityMeasure (densityModel ν p θ))
    (hmeas : ∀ θ ∈ K, Measurable (p θ)) (hpos : ∀ θ ∈ K, ∀ᵐ x ∂ν, 0 < p θ x)
    (hX : AEMeasurable (X 0) P) (hlaw : P.map (X 0) = densityModel ν p θ₀)
    (hint : ∀ θ ∈ K, Integrable (logDensity p θ) (densityModel ν p θ₀))
    (hident : ∀ θ ∈ K, densityModel ν p θ = densityModel ν p θ₀ → θ = θ₀)
    (hcont : ∀ x, ContinuousOn (fun θ => logDensity p θ x) K)
    (hULLN : UniformLLNOn P K (logDensity p) X) {est : ℕ → Ω → Θ}
    (hest : IsMLEOn K (logDensity p) X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 θ₀) :=
  ae_tendsto_of_isMLEOn hK hcont
    (isIdentifiedOn_popCrit_of_densityModel hθ₀ hprob hmeas hpos hX hlaw hint hident) hULLN hest

end Density

end MathlibExt.Probability.Statistics.InformationInequalityIdentification

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.Definitions
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.Condexp

/-!
# MAR as conditional independence and MAR in conditional-mean form

`MissingAtRandomCondIndepFun μ R X hX Y` states missing at random (Rubin 1976) as Mathlib's
conditional independence `R ⊥ Y | σ(X)` of the response `ω ↦ ω ∈ R` and the outcome, on a standard
Borel sample space with a finite measure. The general inverse-weighting theorem
`integral_ipw_treated_condExp`, and its missing-data instance
`integral_ipw_eq_integral_of_mar_condExp`, instead assume the *mean form*
`μ[R.indicator Y | m] =ᵐ μ[R.indicator 1 | m] * μ[Y | m]` for a sub-σ-algebra `m`. This file proves
that the first implies the second, characterizes conditional independence by the mean form for
all transforms of the outcome, and shows that the mean form for the outcome alone is weaker.

## Main results

* `condExp_mul_of_condIndepFun`: if `f ⊥ g | m` for real `f`, `g` with `f`, `g`, `f g` integrable,
  then `E[f g | m] = E[f | m] E[g | m]`. Proved through `condExpKernel`: conditional independence
  makes `f` and `g` independent under almost every conditional law.
* `condExp_indicator_comp_of_condIndepFun`: for any sub-σ-algebra `m`, `R ⊥ Y | m` gives
  `E[1_R g(Y) | m] = P(R | m) E[g(Y) | m]` for every measurable `g` with `g ∘ Y` integrable.
* `MissingAtRandomCondIndepFun.condExp_indicator_comp`: its instance `m = σ(X)`, and
  `MissingAtRandomCondIndepFun.condExp_indicator_mul` for a real integrable outcome (`g = id`),
  which is exactly the hypothesis `hMAR` / `hign` of the inverse-weighting theorems for `σ(X)`.
* `missingAtRandomCondIndepFun_iff_forall_condExp`: MAR holds iff the mean form holds for every
  measurable `g : 𝒴 → ℝ` with `g ∘ Y` integrable (indicators `g = 1_t` suffice).
* `condExp_indicator_mul_of_condIndepDiscrete`: the discrete-covariate MAR condition
  `CondIndepDiscrete μ R Y X` gives the mean form for `σ(X)`.
* `MissingAtRandomCondIndepFun.integral_ipw_eq_integral`: under MAR and strong positivity
  `P(R | σ(X)) ≥ ε > 0`, `E[1_R Y / P(R | σ(X))] = E[Y]`.

The test file shows that the mean form for `Y` alone does not imply MAR: a two-coin outcome
uncorrelated with, but not independent of, the response.

## Not covered

All results keep the standard Borel sample space and finite measure that Mathlib's `CondIndepFun`
requires; conditional independence on a general measurable space is not defined in Mathlib.
The propensity-weighted mean `ipwMean` of the discrete development is not equated here with the
conditional-expectation weighted mean.

## References

* D. B. Rubin, *Inference and missing data*, Biometrika 63(3) (1976), 581–592 (MAR, Section 3).
* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley
  (2019), Section 1.3.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.MissingData

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Causality (CondIndepDiscrete)

variable {Ω 𝒳 𝒴 : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Product rule for conditionally independent real random variables.** If `f ⊥ g | m`
(Mathlib's `CondIndepFun`, on a standard Borel sample space with a finite measure) and `f`, `g`,
`f * g` are integrable, then `E[f g | m] = E[f | m] E[g | m]` almost everywhere. -/
theorem condExp_mul_of_condIndepFun [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : CondIndepFun m hm f g μ) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (f * g) μ) :
    μ[f * g | m] =ᵐ[μ] μ[f | m] * μ[g | m] := by
  have hker := (condIndepFun_iff_map_prod_eq_prod_map_map hf hg).1 hfg
  have hker' : ∀ᵐ ω ∂μ, (condExpKernel μ m).map (fun ω ↦ (f ω, g ω)) ω =
      ((condExpKernel μ m).map f ×ₖ (condExpKernel μ m).map g) ω :=
    ae_of_ae_trim hm hker
  have hind : ∀ᵐ ω ∂μ, IndepFun f g (condExpKernel μ m ω) := hker'.mono fun ω hω => by
    rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable]
    rwa [Kernel.map_apply _ (hf.prodMk hg), Kernel.prod_apply, Kernel.map_apply _ hf,
      Kernel.map_apply _ hg] at hω
  filter_upwards [condExp_ae_eq_integral_condExpKernel hm hfgi,
    condExp_ae_eq_integral_condExpKernel hm hfi, condExp_ae_eq_integral_condExpKernel hm hgi,
    hind] with ω h1 h2 h3 h4
  rw [h1, Pi.mul_apply, h2, h3]
  exact h4.integral_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable

/-! ### MAR implies MAR in conditional-mean form -/

section MAR

variable [m𝒳 : MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

omit [MeasurableSpace 𝒴] in
private lemma measurable_mem_set' {R : Set Ω} (hR : MeasurableSet R) :
    Measurable (· ∈ R : Ω → Prop) :=
  measurableSet_setOfPred.1 hR

omit [MeasurableSpace 𝒴] in
/-- The response indicator `1_R` as a function of the `Prop`-valued response `ω ↦ ω ∈ R`. -/
private lemma indicator_one_eq_comp (R : Set Ω) :
    R.indicator (1 : Ω → ℝ) = (fun p : Prop => by classical exact if p then (1 : ℝ) else 0) ∘
      (· ∈ R) := by
  classical
  funext ω
  by_cases h : ω ∈ R <;> simp [h]

/-- **Conditional independence of the response gives the mean form, for any σ-algebra.** If the
response `ω ↦ ω ∈ R` is conditionally independent of the outcome `Y` given a sub-σ-algebra `m`
(Mathlib's `CondIndepFun`), then for every measurable `g : 𝒴 → ℝ` with `g ∘ Y` integrable,
`E[1_R g(Y) | m] = P(R | m) E[g(Y) | m]` almost everywhere. -/
theorem condExp_indicator_comp_of_condIndepFun [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {R : Set Ω} {Y : Ω → 𝒴} (h : CondIndepFun m hm (· ∈ R) Y μ)
    (hR : MeasurableSet R) (hY : Measurable Y) {g : 𝒴 → ℝ} (hg : Measurable g)
    (hgY : Integrable (g ∘ Y) μ) :
    μ[R.indicator (g ∘ Y) | m] =ᵐ[μ] fun ω => μ[R.indicator 1 | m] ω * μ[g ∘ Y | m] ω := by
  have hφ : Measurable (fun p : Prop => by classical exact if p then (1 : ℝ) else 0) :=
    .of_discrete
  have hCI : CondIndepFun m hm (R.indicator (1 : Ω → ℝ)) (g ∘ Y) μ := by
    rw [indicator_one_eq_comp]
    exact CondIndepFun.comp h hφ hg
  have hRi : Integrable (R.indicator (1 : Ω → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hR
  have hmul : R.indicator (g ∘ Y) = R.indicator (1 : Ω → ℝ) * (g ∘ Y) := by
    funext ω
    by_cases hω : ω ∈ R <;> simp [hω]
  rw [hmul]
  refine condExp_mul_of_condIndepFun hm (measurable_const.indicator hR) (hg.comp hY) hCI hRi hgY ?_
  rw [← hmul]
  exact hgY.indicator hR

/-- **MAR gives mean MAR for every transform of the outcome.** If the response `R` is
conditionally independent of the outcome `Y` given `σ(X)` (`MissingAtRandomCondIndepFun`), then
for every measurable `g : 𝒴 → ℝ` with `g ∘ Y` integrable,
`E[1_R g(Y) | σ(X)] = P(R | σ(X)) E[g(Y) | σ(X)]` almost everywhere. The instance
`m = σ(X)` of `condExp_indicator_comp_of_condIndepFun`. -/
theorem MissingAtRandomCondIndepFun.condExp_indicator_comp [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] {R : Set Ω} {X : Ω → 𝒳} {hX : Measurable X} {Y : Ω → 𝒴}
    (h : MissingAtRandomCondIndepFun μ R X hX Y) (hR : MeasurableSet R) (hY : Measurable Y)
    {g : 𝒴 → ℝ} (hg : Measurable g) (hgY : Integrable (g ∘ Y) μ) :
    μ[R.indicator (g ∘ Y) | m𝒳.comap X] =ᵐ[μ]
      fun ω => μ[R.indicator 1 | m𝒳.comap X] ω * μ[g ∘ Y | m𝒳.comap X] ω :=
  condExp_indicator_comp_of_condIndepFun hX.comap_le h hR hY hg hgY

/-- **MAR gives the mean-MAR hypothesis of inverse weighting.** For a real integrable outcome,
`MissingAtRandomCondIndepFun` implies `E[1_R Y | σ(X)] = P(R | σ(X)) E[Y | σ(X)]` almost
everywhere: the hypothesis `hMAR` of `integral_ipw_eq_integral_of_mar_condExp` and `hign` of
`integral_ipw_treated_condExp`, for the σ-algebra `m = σ(X)`. -/
theorem MissingAtRandomCondIndepFun.condExp_indicator_mul [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] {R : Set Ω} {X : Ω → 𝒳} {hX : Measurable X} {Y : Ω → ℝ}
    (h : MissingAtRandomCondIndepFun μ R X hX Y) (hR : MeasurableSet R) (hY : Measurable Y)
    (hYi : Integrable Y μ) :
    μ[R.indicator Y | m𝒳.comap X] =ᵐ[μ]
      fun ω => μ[R.indicator 1 | m𝒳.comap X] ω * μ[Y | m𝒳.comap X] ω :=
  h.condExp_indicator_comp hR hY measurable_id hYi

/-- **Discrete MAR gives the mean form.** For a countably valued covariate with measurable
singletons on a standard Borel sample space, the discrete conditional independence
`CondIndepDiscrete μ R Y X` (equivalently `MissingOutcomes.MissingAtRandom μ R Y X`) implies
`E[1_R Y | σ(X)] = P(R | σ(X)) E[Y | σ(X)]` almost everywhere, through
`missingAtRandomCondIndepFun_iff_condIndepDiscrete`. -/
theorem condExp_indicator_mul_of_condIndepDiscrete [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    [Countable 𝒳] [MeasurableSingletonClass 𝒳] {R : Set Ω} {X : Ω → 𝒳} {Y : Ω → ℝ}
    (h : CondIndepDiscrete μ R Y X) (hR : MeasurableSet R) (hX : Measurable X)
    (hY : Measurable Y) (hYi : Integrable Y μ) :
    μ[R.indicator Y | m𝒳.comap X] =ᵐ[μ]
      fun ω => μ[R.indicator 1 | m𝒳.comap X] ω * μ[Y | m𝒳.comap X] ω :=
  ((missingAtRandomCondIndepFun_iff_condIndepDiscrete hR hX hY).2 h).condExp_indicator_mul hR hY
    hYi

omit [MeasurableSpace 𝒴] in
/-- A set of propositions pulls back under `ω ↦ ω ∈ R` to `∅`, `R`, `Rᶜ` or everything. -/
private lemma preimage_mem_cases' (R : Set Ω) (s : Set Prop) :
    (· ∈ R) ⁻¹' s = ∅ ∨ (· ∈ R) ⁻¹' s = R ∨ (· ∈ R) ⁻¹' s = Rᶜ ∨
      (· ∈ R) ⁻¹' s = Set.univ := by
  by_cases h1 : True ∈ s <;> by_cases h2 : False ∈ s
  · refine Or.inr (Or.inr (Or.inr ?_))
    ext ω; by_cases h : ω ∈ R <;> simp [h, h1, h2]
  · refine Or.inr (Or.inl ?_)
    ext ω; by_cases h : ω ∈ R <;> simp [h, h1, h2]
  · refine Or.inr (Or.inr (Or.inl ?_))
    ext ω; by_cases h : ω ∈ R <;> simp [h, h1, h2]
  · refine Or.inl ?_
    ext ω; by_cases h : ω ∈ R <;> simp [h, h1, h2]

/-- **MAR is mean MAR for all transforms of the outcome.** On a standard Borel sample space with a
finite measure, `MissingAtRandomCondIndepFun μ R X hX Y` holds iff for every measurable
`g : 𝒴 → ℝ` with `g ∘ Y` integrable, `E[1_R g(Y) | σ(X)] = P(R | σ(X)) E[g(Y) | σ(X)]` almost
everywhere. The reverse direction uses only indicators `g = 1_t`. -/
theorem missingAtRandomCondIndepFun_iff_forall_condExp [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] {R : Set Ω} {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → 𝒴}
    (hR : MeasurableSet R) (hY : Measurable Y) :
    MissingAtRandomCondIndepFun μ R X hX Y ↔
      ∀ g : 𝒴 → ℝ, Measurable g → Integrable (g ∘ Y) μ →
        μ[R.indicator (g ∘ Y) | m𝒳.comap X] =ᵐ[μ]
          fun ω => μ[R.indicator 1 | m𝒳.comap X] ω * μ[g ∘ Y | m𝒳.comap X] ω := by
  refine ⟨fun h g hg hgY => h.condExp_indicator_comp hR hY hg hgY, fun H => ?_⟩
  have hm : m𝒳.comap X ≤ mΩ := hX.comap_le
  rw [MissingAtRandomCondIndepFun,
    condIndepFun_iff_condExp_inter_preimage_eq_mul (measurable_mem_set' hR) hY]
  intro s t _ ht
  have hYt : MeasurableSet (Y ⁻¹' t) := hY ht
  have hcomp : t.indicator (1 : 𝒴 → ℝ) ∘ Y = (Y ⁻¹' t).indicator 1 := by
    funext ω; by_cases hω : Y ω ∈ t <;> simp [hω]
  have key := H (t.indicator 1) (measurable_const.indicator ht)
    (by rw [hcomp]; exact (integrable_const (1 : ℝ)).indicator hYt)
  rw [hcomp, Set.indicator_indicator] at key
  have hone : μ[(fun _ => (1 : ℝ)) | m𝒳.comap X] = fun _ => 1 := condExp_const hm 1
  rcases preimage_mem_cases' R s with hs | hs | hs | hs <;> rw [hs]
  · simp only [Set.empty_inter, Set.indicator_empty]
    exact Filter.EventuallyEq.rfl.trans (ae_of_all _ fun ω => by simp)
  · exact key
  · -- `1_{Rᶜ ∩ B} = 1_B - 1_{R ∩ B}` and `1_{Rᶜ} = 1 - 1_R`
    have hi1 : (Rᶜ ∩ Y ⁻¹' t).indicator (fun _ => (1 : ℝ)) =
        (Y ⁻¹' t).indicator (fun _ => (1 : ℝ)) - (R ∩ Y ⁻¹' t).indicator (fun _ => (1 : ℝ)) := by
      funext ω; by_cases h1 : ω ∈ R <;> by_cases h2 : ω ∈ Y ⁻¹' t <;> simp [h1, h2]
    have hi2 : Rᶜ.indicator (fun _ => (1 : ℝ)) =
        (fun _ => (1 : ℝ)) - R.indicator (fun _ => (1 : ℝ)) := by
      funext ω; by_cases h1 : ω ∈ R <;> simp [h1]
    have hBi : Integrable ((Y ⁻¹' t).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hYt
    have hRBi : Integrable ((R ∩ Y ⁻¹' t).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator (hR.inter hYt)
    have hRi : Integrable (R.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hR
    rw [hi1, hi2]
    filter_upwards [condExp_sub hBi hRBi (m := m𝒳.comap X),
      condExp_sub (integrable_const (1 : ℝ)) hRi (m := m𝒳.comap X), key] with ω h1 h2 h3
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, hone]
    change _ - _ = (1 - _) * _
    rw [show μ[(R ∩ Y ⁻¹' t).indicator (fun _ => (1 : ℝ)) | m𝒳.comap X] ω =
      μ[R.indicator (fun _ => (1 : ℝ)) | m𝒳.comap X] ω *
        μ[(Y ⁻¹' t).indicator (fun _ => (1 : ℝ)) | m𝒳.comap X] ω from h3]
    ring
  · simp only [Set.univ_inter, Set.indicator_univ]
    exact ae_of_all _ fun ω => by simp [hone]

/-- **Inverse weighting under MAR.** For a real integrable outcome that is missing at random
given `X` (`MissingAtRandomCondIndepFun`, standard Borel sample space) and strong response
positivity `P(R | σ(X)) ≥ ε > 0`, the inverse-response-weighted mean of the respondents'
outcomes identifies `E[Y]`. This discharges the mean-MAR hypothesis of the general inverse
weighting theorem `integral_ipw_treated_condExp` by
`MissingAtRandomCondIndepFun.condExp_indicator_mul`. -/
theorem MissingAtRandomCondIndepFun.integral_ipw_eq_integral [StandardBorelSpace Ω]
    [IsProbabilityMeasure μ] {R : Set Ω} {X : Ω → 𝒳} {hX : Measurable X} {Y : Ω → ℝ}
    (h : MissingAtRandomCondIndepFun μ R X hX Y) (hR : MeasurableSet R) (hY : Measurable Y)
    (hYi : Integrable Y μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ μ[R.indicator 1 | m𝒳.comap X] ω) :
    ∫ ω, R.indicator (fun ω => Y ω / μ[R.indicator 1 | m𝒳.comap X] ω) ω ∂μ = ∫ ω, Y ω ∂μ := by
  rw [← integral_ipw_treated_condExp hX.comap_le hR (Y₀ := 0) hYi
    (h.condExp_indicator_mul hR hY hYi) hε hpos]
  congr 1
  funext ω
  by_cases hω : ω ∈ R <;> simp [MathlibExt.Probability.Causality.observed, hω]

end MAR

end MathlibExt.Probability.Causality.MissingData

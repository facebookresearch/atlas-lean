/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.GeneralIPW
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.Condexp

/-!
# MAR as conditional independence: the product rule and the converse of mean MAR

`MissingAtRandomCondIndepFun μ R X hX Y` states missing at random (Rubin 1976) as Mathlib's
conditional independence `R ⊥ Y | σ(X)` of the response `ω ↦ ω ∈ R` and the outcome, on a standard
Borel sample space with a finite measure. `MissingData.GeneralIPW` derives from it two forms, and
the inverse-weighting theorems assume different ones:

* the *set-wise form* `P(R ∩ {Y ∈ S} | σ(X)) = P(R | σ(X)) P(Y ∈ S | σ(X))` for every measurable
  `S` (`condExp_inter_preimage_ae_eq_mul_of_condIndepFun`), the hypothesis `hMAR` of
  `integral_ipw_eq_integral_of_mar_sigma` in `MissingData.GeneralIPW`;
* the *mean form* `μ[R.indicator Y | m] =ᵐ μ[R.indicator 1 | m] * μ[Y | m]`, obtained from the
  set-wise form by `condExp_indicator_ae_eq_mul_of_mar`, the hypothesis `hMAR` of
  `integral_ipw_eq_integral_of_mar_condExp` in `MissingData.Identification`.

The mean form is the weaker statement and does not discharge the set-wise `hMAR` (the test file
has an outcome with the mean form but not MAR). This file proves the product rule for
conditionally independent real random variables, the converse (the mean form for every transform
of the outcome implies MAR), and, for a countably valued covariate, both forms from the discrete
conditional independence `CondIndepDiscrete μ R Y X` on any sample space.

## Main results

* `condExp_mul_of_condIndepFun`: if `f ⊥ g | m` for real `f`, `g` with `f`, `g`, `f g` integrable,
  then `E[f g | m] = E[f | m] E[g | m]`. Proved through `condExpKernel`: conditional independence
  makes `f` and `g` independent under almost every conditional law.
* `missingAtRandomCondIndepFun_iff_forall_condExp`: MAR holds iff the mean form holds for every
  measurable `g : 𝒴 → ℝ` with `g ∘ Y` integrable. The forward direction is the `GeneralIPW`
  bridge applied to `g ∘ Y`. The converse uses only indicators `g = 1_t`, that is the set-wise
  form `P(R ∩ {Y ∈ t} | σ(X)) = P(R | σ(X)) P(Y ∈ t | σ(X))`, and gets the other events
  `∅, Rᶜ, Ω` of `σ(R)` by linearity of conditional expectation.
* `condExp_inter_preimage_ae_eq_mul_of_condIndepDiscrete`: for a countably valued `X` with
  measurable singletons and a finite measure, `CondIndepDiscrete μ R Y X` gives the set-wise form,
  with no standard Borel assumption. Each conditional probability given `σ(X)` is a propensity at
  `X ω` (`condExp_indicator_comap_ae_eq`), so the set-wise form is checked value by value.
* `condExp_indicator_mul_of_condIndepDiscrete`: on the same domain, `CondIndepDiscrete μ R Y X`
  gives the mean form for an integrable real outcome, through the set-wise form and
  `condExp_indicator_ae_eq_mul_of_mar`. On a standard Borel space it also follows from
  `missingAtRandomCondIndepFun_iff_condIndepDiscrete`; this proof does not use that bridge.

The test file shows that the mean form for `Y` alone does not imply MAR: a two-coin outcome
uncorrelated with, but not independent of, the response. It also applies the discrete results on
a sample space that is not standard Borel, and gives a missing-not-at-random law on that space
where `CondIndepDiscrete` and the set-wise form both fail.

## Not covered

The results about `CondIndepFun` and `MissingAtRandomCondIndepFun` keep the standard Borel sample
space and finite measure that Mathlib's `CondIndepFun` requires; conditional independence on a
general measurable space is not defined in Mathlib. The discrete results drop the standard Borel
assumption only for a countably valued covariate with measurable singletons; a covariate with
uncountably many values on a sample space that is not standard Borel is not covered. The converse
is proved for the covariate σ-algebra `σ(X)` only, not for a general sub-σ-algebra.

## References

* D. B. Rubin, *Inference and missing data*, Biometrika 63(3) (1976), 581–592 (MAR, Section 3).
* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley
  (2019), Section 1.3.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.MissingData

open MeasureTheory ProbabilityTheory

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

/-! ### MAR is mean MAR for every transform of the outcome -/

section MAR

variable [m𝒳 : MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

/-- **MAR is mean MAR for all transforms of the outcome.** On a standard Borel sample space with a
finite measure, `MissingAtRandomCondIndepFun μ R X hX Y` holds iff for every measurable
`g : 𝒴 → ℝ` with `g ∘ Y` integrable, `E[1_R g(Y) | σ(X)] = P(R | σ(X)) E[g(Y) | σ(X)]` almost
everywhere. The forward direction is `condExp_inter_preimage_ae_eq_mul_of_condIndepFun` followed
by `condExp_indicator_ae_eq_mul_of_mar`, applied to `g ∘ Y`. The reverse direction uses only
indicators `g = 1_t`. -/
theorem missingAtRandomCondIndepFun_iff_forall_condExp [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] {R : Set Ω} {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → 𝒴}
    (hR : MeasurableSet R) (hY : Measurable Y) :
    MissingAtRandomCondIndepFun μ R X hX Y ↔
      ∀ g : 𝒴 → ℝ, Measurable g → Integrable (g ∘ Y) μ →
        μ[R.indicator (g ∘ Y) | m𝒳.comap X] =ᵐ[μ]
          fun ω => μ[R.indicator 1 | m𝒳.comap X] ω * μ[g ∘ Y | m𝒳.comap X] ω := by
  have hm : m𝒳.comap X ≤ mΩ := hX.comap_le
  refine ⟨fun h g hg hgY => condExp_indicator_ae_eq_mul_of_mar hm hR (hg.comp hY) hgY
    (condExp_inter_preimage_ae_eq_mul_of_condIndepFun hm hR (hg.comp hY)
      (CondIndepFun.comp (φ := id) (ψ := g) h measurable_id hg)), fun H => ?_⟩
  rw [MissingAtRandomCondIndepFun,
    condIndepFun_iff_condExp_inter_preimage_eq_mul (measurable_mem_set hR) hY]
  intro s t _ ht
  have hYt : MeasurableSet (Y ⁻¹' t) := hY ht
  have hcomp : t.indicator (1 : 𝒴 → ℝ) ∘ Y = (Y ⁻¹' t).indicator 1 := by
    funext ω; by_cases hω : Y ω ∈ t <;> simp [hω]
  have key := H (t.indicator 1) (measurable_const.indicator ht)
    (by rw [hcomp]; exact (integrable_const (1 : ℝ)).indicator hYt)
  rw [hcomp, Set.indicator_indicator] at key
  have hone : μ[(fun _ => (1 : ℝ)) | m𝒳.comap X] = fun _ => 1 := condExp_const hm 1
  rcases preimage_mem_cases R s with hs | hs | hs | hs <;> rw [hs]
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

/-! ### Discrete MAR without a standard Borel sample space -/

omit m𝒳 [MeasurableSpace 𝒴] in
/-- For a countably valued `X`, almost every `ω` has `P(X = X ω) ≠ 0`. -/
private lemma ae_measure_preimage_singleton_ne_zero [Countable 𝒳] {X : Ω → 𝒳} :
    ∀ᵐ ω ∂μ, μ (X ⁻¹' {X ω}) ≠ 0 := by
  have hsub : {ω | ¬μ (X ⁻¹' {X ω}) ≠ 0} ⊆ ⋃ x : {x : 𝒳 // μ (X ⁻¹' {x}) = 0}, X ⁻¹' {x.1} :=
    fun ω hω => Set.mem_iUnion.2 ⟨⟨X ω, not_not.1 hω⟩, rfl⟩
  exact ae_iff.2 (measure_mono_null hsub (measure_iUnion_null fun x => x.2))

/-- **Discrete MAR gives set-wise MAR given `σ(X)`, on any sample space.** For a countably valued
covariate `X` with measurable singletons and a finite measure, the discrete conditional
independence `CondIndepDiscrete μ R Y X` implies
`P(R ∩ {Y ∈ S} | σ(X)) = P(R | σ(X)) P(Y ∈ S | σ(X))` almost everywhere for every measurable `S`.
No standard Borel assumption: each conditional probability is the propensity at `X ω`
(`condExp_indicator_comap_ae_eq`), and at a value of positive probability the propensity product
rule is `CondIndepDiscrete`. For a real outcome this is the set-wise hypothesis `hMAR` of
`condExp_indicator_ae_eq_mul_of_mar` and `integral_ipw_eq_integral_of_mar_sigma`. -/
theorem condExp_inter_preimage_ae_eq_mul_of_condIndepDiscrete [IsFiniteMeasure μ] [Countable 𝒳]
    [MeasurableSingletonClass 𝒳] {R : Set Ω} {X : Ω → 𝒳} {Y : Ω → 𝒴}
    (h : CondIndepDiscrete μ R Y X) (hR : MeasurableSet R) (hX : Measurable X)
    (hY : Measurable Y) :
    ∀ S, MeasurableSet S →
      (μ⟦R ∩ Y ⁻¹' S | m𝒳.comap X⟧) =ᵐ[μ] (μ⟦R | m𝒳.comap X⟧) * (μ⟦Y ⁻¹' S | m𝒳.comap X⟧) := by
  intro S hS
  filter_upwards [condExp_indicator_comap_ae_eq (μ := μ) hX (hR.inter (hY hS)),
    condExp_indicator_comap_ae_eq (μ := μ) hX hR, condExp_indicator_comap_ae_eq (μ := μ) hX (hY hS),
    ae_measure_preimage_singleton_ne_zero (μ := μ) (X := X)] with ω h1 h2 h3 hω
  rw [h1, Pi.mul_apply, h2, h3]
  have hx : μ.real (X ⁻¹' {X ω}) ≠ 0 := (measureReal_eq_zero_iff).not.2 hω
  rw [propensity, propensity, propensity, div_mul_div_comm,
    div_eq_div_iff hx (mul_ne_zero hx hx), ← mul_assoc, mul_left_inj' hx]
  exact h S hS (X ω)

/-- **Discrete MAR gives mean MAR, on any sample space.** For a countably valued covariate `X`
with measurable singletons, a finite measure and an integrable real outcome,
`CondIndepDiscrete μ R Y X` implies `E[1_R Y | σ(X)] = P(R | σ(X)) E[Y | σ(X)]` almost everywhere:
the mean-form hypothesis `hMAR` of `integral_ipw_eq_integral_of_mar_condExp`. Proved by
`condExp_inter_preimage_ae_eq_mul_of_condIndepDiscrete` and
`condExp_indicator_ae_eq_mul_of_mar`, with no standard Borel assumption. -/
theorem condExp_indicator_mul_of_condIndepDiscrete [IsFiniteMeasure μ] [Countable 𝒳]
    [MeasurableSingletonClass 𝒳] {R : Set Ω} {X : Ω → 𝒳} {Y : Ω → ℝ}
    (h : CondIndepDiscrete μ R Y X) (hR : MeasurableSet R) (hX : Measurable X)
    (hY : Measurable Y) (hYi : Integrable Y μ) :
    μ[R.indicator Y | m𝒳.comap X] =ᵐ[μ]
      fun ω => μ[R.indicator 1 | m𝒳.comap X] ω * μ[Y | m𝒳.comap X] ω :=
  condExp_indicator_ae_eq_mul_of_mar hX.comap_le hR hY hYi
    (condExp_inter_preimage_ae_eq_mul_of_condIndepDiscrete h hR hX hY)

end MAR

end MathlibExt.Probability.Causality.MissingData

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
Borel sample space with a finite measure. `MissingData.GeneralIPW` derives from it the *mean form*
`μ[R.indicator Y | m] =ᵐ μ[R.indicator 1 | m] * μ[Y | m]` that the inverse-weighting theorems
assume (`condExp_inter_preimage_ae_eq_mul_of_condIndepFun`, then
`condExp_indicator_ae_eq_mul_of_mar`). This file proves the product rule for conditionally
independent real random variables and the converse: the mean form for every transform of the
outcome implies MAR.

## Main results

* `condExp_mul_of_condIndepFun`: if `f ⊥ g | m` for real `f`, `g` with `f`, `g`, `f g` integrable,
  then `E[f g | m] = E[f | m] E[g | m]`. Proved through `condExpKernel`: conditional independence
  makes `f` and `g` independent under almost every conditional law.
* `missingAtRandomCondIndepFun_iff_forall_condExp`: MAR holds iff the mean form holds for every
  measurable `g : 𝒴 → ℝ` with `g ∘ Y` integrable. The forward direction is the `GeneralIPW`
  bridge applied to `g ∘ Y`. The converse uses only indicators `g = 1_t`, that is the set-wise
  form `P(R ∩ {Y ∈ t} | σ(X)) = P(R | σ(X)) P(Y ∈ t | σ(X))`, and gets the other events
  `∅, Rᶜ, Ω` of `σ(R)` by linearity of conditional expectation.

The test file shows that the mean form for `Y` alone does not imply MAR: a two-coin outcome
uncorrelated with, but not independent of, the response.

## Not covered

All results keep the standard Borel sample space and finite measure that Mathlib's `CondIndepFun`
requires; conditional independence on a general measurable space is not defined in Mathlib. The
converse is proved for the covariate σ-algebra `σ(X)` only, not for a general sub-σ-algebra.

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

end MAR

end MathlibExt.Probability.Causality.MissingData

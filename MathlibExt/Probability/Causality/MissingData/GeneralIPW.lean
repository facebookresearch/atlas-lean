/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.Identification

/-!
# Inverse-response weighting under MAR with a general covariate σ-algebra

An outcome `Y : Ω → ℝ` is observed only on the response event `R`; the always-observed covariate
information is an arbitrary sub-σ-algebra `m` (for example `σ(X)` for a covariate `X` with values
in any measurable space). Write `P(E | m) = μ⟦E | m⟧` for the conditional probability given `m`
and `π = P(R | m)` for the response probability.

**Missing at random** given `m` is taken here in a set-wise conditional-expectation form of the
conditional independence `R ⊥ Y | m`, one equation for every event of `Y`:

`P(R ∩ {Y ∈ S} | m) = P(R | m) P(Y ∈ S | m)` almost everywhere, for every measurable `S ⊆ ℝ`.

This form needs no regularity of the sample space. When `Ω` is standard Borel it is the
instance `s = {True}` of Mathlib's `condIndepFun_iff_condExp_inter_preimage_eq_mul` for the
response indicator `ω ↦ ω ∈ R` and `Y`, so Mathlib's `CondIndepFun` implies it
(`condExp_inter_preimage_ae_eq_mul_of_condIndepFun`); in particular so does
`MissingAtRandomCondIndepFun` from `MissingData.Definitions`, with `m = σ(X)`. The remaining
events `∅, Rᶜ, Ω` of `σ(R)` add nothing, since conditional expectation is linear;
`missingAtRandomCondIndepFun_iff_forall_condExp` in `MissingData.MARBridge` uses this to prove the
converse for `m = σ(X)`, from mean MAR for every transform of `Y`.

The general inverse-weighting theorem `integral_ipw_eq_integral_of_mar_condExp` (in
`MissingData.Identification`, an instance of `integral_ipw_treated_condExp`) assumes only *mean*
MAR, `E[1_R Y | m] = π E[Y | m]`. This file derives mean MAR from MAR, so that the weighted mean
`E[1_R Y / π]` identifies `E[Y]` under this set-wise MAR assumption.

## Main results

* `condExp_inter_preimage_ae_eq_mul_of_condIndepFun`: on a standard Borel space, Mathlib's
  conditional independence `CondIndepFun m hm (· ∈ R) Y μ` implies MAR given `m` in the set-wise
  form above.
* `condExp_indicator_ae_eq_mul_of_mar`: MAR given `m` and integrability of `Y` imply mean MAR,
  `E[1_R Y | m] = P(R | m) E[Y | m]` almost everywhere.
* `integral_ipw_eq_integral_of_mar_sigma`: **identification**. Under MAR given `m` and strong
  positivity `P(R | m) ≥ ε > 0`, the inverse-response-weighted mean `E[1_R Y / P(R | m)]` equals
  the full-data mean `E[Y]`.
* `integrable_ipw_condExp_of_pos`: under strong positivity alone, the weighted outcome
  `1_R Y / P(R | m)` is integrable.

## Proof idea

For an `m`-measurable `A`, MAR and the pull-out property give, for every event `{Y ∈ S}`,
`μ(A ∩ R ∩ {Y ∈ S}) = ∫_A π 1_{Y ∈ S}`. So the image under `Y` of `μ` restricted to `A ∩ R` and
the image under `Y` of `μ` restricted to `A` with density `π` are the same measure on `ℝ`;
comparing their means gives `∫_A 1_R Y = ∫_A π Y = ∫_A π E[Y | m]`, which characterizes
`E[1_R Y | m]`.

## Not covered

* The converse of `condExp_inter_preimage_ae_eq_mul_of_condIndepFun` (set-wise MAR implies
  `CondIndepFun`) for a general sub-σ-algebra `m`. For `m = σ(X)`,
  `missingAtRandomCondIndepFun_iff_forall_condExp` in `MissingData.MARBridge` proves that mean MAR
  for every measurable transform `g ∘ Y` implies `MissingAtRandomCondIndepFun`; set-wise MAR gives
  that hypothesis through `condExp_indicator_ae_eq_mul_of_mar` applied to `g ∘ Y`.
* Any bridge to `CondIndepFun` without a standard Borel sample space.
* Weak positivity (`π > 0` without a uniform lower bound), estimation of `π`, and asymptotics.

## References

* D. B. Rubin, *Inference and missing data*, Biometrika 63(3) (1976), 581–592.
* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley
  (2019), Section 1.3 and Chapter 3.
* D. G. Horvitz and D. J. Thompson, *A generalization of sampling without replacement from a
  finite universe*, JASA 47(260) (1952), 663–685.
* A. A. Tsiatis, *Semiparametric Theory and Missing Data*, Springer (2006), Chapter 6.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.MissingData

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section MARSigma

/-- The conditional probability of an event takes values in `[0, 1]`; here `|P(E | m)| ≤ 1`. -/
private lemma abs_condExp_indicator_le_one (E : Set Ω) :
    ∀ᵐ ω ∂μ, |(μ⟦E | m⟧) ω| ≤ 1 := by
  refine ae_bdd_abs_condExp_of_ae_bdd_abs (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ E <;> simp [hω]

private lemma condExp_indicator_nonneg (E : Set Ω) : 0 ≤ᵐ[μ] μ⟦E | m⟧ :=
  condExp_nonneg (Filter.Eventually.of_forall fun _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- `P(E | m) g` is integrable for an integrable `g`. -/
private lemma integrable_condExp_indicator_mul (hm : m ≤ mΩ) (E : Set Ω) {g : Ω → ℝ}
    (hg : Integrable g μ) : Integrable (μ⟦E | m⟧ * g) μ :=
  hg.bdd_mul (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
    ((abs_condExp_indicator_le_one (m := m) E).mono fun _ h => by simpa using h)

variable [IsFiniteMeasure μ]

/-- Pull-out on an `m`-measurable set: `∫_A P(E | m) E[g | m] = ∫_A P(E | m) g`. -/
private lemma setIntegral_condExp_indicator_mul (hm : m ≤ mΩ) (E : Set Ω) {g : Ω → ℝ}
    (hg : Integrable g μ) {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫ ω in A, ((μ⟦E | m⟧) * μ[g | m]) ω ∂μ = ∫ ω in A, ((μ⟦E | m⟧) * g) ω ∂μ := by
  rw [← setIntegral_condExp hm (integrable_condExp_indicator_mul hm E hg) hA]
  exact setIntegral_congr_ae (hm A hA) <|
    (condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp
      (integrable_condExp_indicator_mul hm E hg) hg).mono fun _ h _ => h.symm

/-- Under MAR, for `A ∈ m` and every event `{Y ∈ S}`:
`μ(A ∩ (R ∩ {Y ∈ S})) = ∫_A P(R | m) 1_{Y ∈ S}`. -/
private lemma measureReal_inter_eq_setIntegral (hm : m ≤ mΩ) {R : Set Ω} (hR : MeasurableSet R)
    {Y : Ω → ℝ} (hY : Measurable Y)
    (hMAR : ∀ S, MeasurableSet S →
      (μ⟦R ∩ Y ⁻¹' S | m⟧) =ᵐ[μ] (μ⟦R | m⟧) * (μ⟦Y ⁻¹' S | m⟧))
    {A : Set Ω} (hA : MeasurableSet[m] A) {S : Set ℝ} (hS : MeasurableSet S) :
    μ.real (A ∩ (R ∩ Y ⁻¹' S)) =
      ∫ ω in A, ((μ⟦R | m⟧) * (Y ⁻¹' S).indicator fun _ => (1 : ℝ)) ω ∂μ := by
  have hB : MeasurableSet (Y ⁻¹' S) := hY hS
  rw [← setIntegral_condExp_indicator_mul hm R
      ((integrable_const (1 : ℝ)).indicator hB) hA,
    ← setIntegral_congr_ae (hm A hA) ((hMAR S hS).mono fun _ h _ => h),
    setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator (hR.inter hB)) hA,
    integral_indicator (hR.inter hB), Measure.restrict_restrict (hR.inter hB), setIntegral_const,
    smul_eq_mul, mul_one, Set.inter_comm]

/-- The key identity: under MAR, `∫_A 1_R Y = ∫_A P(R | m) Y` for every `A ∈ m`. The images
under `Y` of `μ` on `A ∩ R` and of `μ` on `A` with density `P(R | m)` agree on every event, so
they have the same mean. -/
private lemma setIntegral_indicator_eq_setIntegral_mul (hm : m ≤ mΩ) {R : Set Ω}
    (hR : MeasurableSet R) {Y : Ω → ℝ} (hY : Measurable Y)
    (hMAR : ∀ S, MeasurableSet S →
      (μ⟦R ∩ Y ⁻¹' S | m⟧) =ᵐ[μ] (μ⟦R | m⟧) * (μ⟦Y ⁻¹' S | m⟧))
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫ ω in A, R.indicator Y ω ∂μ = ∫ ω in A, ((μ⟦R | m⟧) * Y) ω ∂μ := by
  set π : Ω → ℝ := μ⟦R | m⟧ with hπ
  have hπm : Measurable π := (stronglyMeasurable_condExp.mono hm).measurable
  set ρ : Ω → ENNReal := fun ω => ENNReal.ofReal (π ω) with hρ
  have hρm : Measurable ρ := ENNReal.measurable_ofReal.comp hπm
  have hmap : (μ.restrict (A ∩ R)).map Y = ((μ.restrict A).withDensity ρ).map Y := by
    ext S hS
    have hB : MeasurableSet (Y ⁻¹' S) := hY hS
    have hint : Integrable (π * (Y ⁻¹' S).indicator fun _ => (1 : ℝ)) μ :=
      integrable_condExp_indicator_mul hm R ((integrable_const (1 : ℝ)).indicator hB)
    rw [Measure.map_apply hY hS, Measure.map_apply hY hS, Measure.restrict_apply hB,
      withDensity_apply _ hB, Measure.restrict_restrict hB]
    calc μ (Y ⁻¹' S ∩ (A ∩ R))
        = ENNReal.ofReal (μ.real (A ∩ (R ∩ Y ⁻¹' S))) := by
          rw [ofReal_measureReal]
          congr 1
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_preimage]
          tauto
      _ = ENNReal.ofReal (∫ ω in A, (π * (Y ⁻¹' S).indicator fun _ => (1 : ℝ)) ω ∂μ) := by
          rw [measureReal_inter_eq_setIntegral hm hR hY hMAR hA hS]
      _ = ∫⁻ ω in A, ENNReal.ofReal ((π * (Y ⁻¹' S).indicator fun _ => (1 : ℝ)) ω) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal hint.integrableOn
            (ae_restrict_of_ae ((condExp_indicator_nonneg (m := m) R).mono fun ω h =>
              mul_nonneg h (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)))
      _ = ∫⁻ ω in A, (Y ⁻¹' S).indicator ρ ω ∂μ := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ Y ⁻¹' S <;> simp [hω, hρ]
      _ = ∫⁻ ω in Y ⁻¹' S ∩ A, ρ ω ∂μ := by
          rw [lintegral_indicator hB, Measure.restrict_restrict hB]
  calc ∫ ω in A, R.indicator Y ω ∂μ
      = ∫ ω, Y ω ∂(μ.restrict (A ∩ R)) := by
        rw [integral_indicator hR, Measure.restrict_restrict hR, Set.inter_comm]
    _ = ∫ y, y ∂((μ.restrict (A ∩ R)).map Y) :=
        (integral_map hY.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ y, y ∂(((μ.restrict A).withDensity ρ).map Y) := by rw [hmap]
    _ = ∫ ω, Y ω ∂((μ.restrict A).withDensity ρ) :=
        integral_map hY.aemeasurable aestronglyMeasurable_id
    _ = ∫ ω in A, (ρ ω).toReal • Y ω ∂μ :=
        integral_withDensity_eq_integral_toReal_smul hρm
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _
    _ = ∫ ω in A, (π * Y) ω ∂μ := by
        refine integral_congr_ae ((ae_restrict_of_ae (condExp_indicator_nonneg (m := m) R)).mono
          fun ω h => ?_)
        change (ENNReal.ofReal (π ω)).toReal * Y ω = π ω * Y ω
        rw [ENNReal.toReal_ofReal h]

/-- **MAR implies mean MAR, general covariate σ-algebra.** Let `m ≤ mΩ` be the always-observed
covariate information, `R` the response event and `Y` an integrable outcome. If `R ⊥ Y | m` in
the form `P(R ∩ {Y ∈ S} | m) = P(R | m) P(Y ∈ S | m)` a.e. for every measurable `S`, then
`E[1_R Y | m] = P(R | m) E[Y | m]` almost everywhere. -/
theorem condExp_indicator_ae_eq_mul_of_mar (hm : m ≤ mΩ) {R : Set Ω} (hR : MeasurableSet R)
    {Y : Ω → ℝ} (hY : Measurable Y) (hYi : Integrable Y μ)
    (hMAR : ∀ S, MeasurableSet S →
      (μ⟦R ∩ Y ⁻¹' S | m⟧) =ᵐ[μ] (μ⟦R | m⟧) * (μ⟦Y ⁻¹' S | m⟧)) :
    μ[R.indicator Y | m] =ᵐ[μ] (μ⟦R | m⟧) * μ[Y | m] := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hYi.indicator hR)
    (fun s _ _ => (integrable_condExp_indicator_mul hm R integrable_condExp).integrableOn)
    (fun s hs _ => ?_)
    (stronglyMeasurable_condExp.mul stronglyMeasurable_condExp).aestronglyMeasurable).symm
  rw [setIntegral_condExp_indicator_mul hm R hYi hs,
    setIntegral_indicator_eq_setIntegral_mul hm hR hY hMAR hs]

/-- **Conditional independence implies set-wise MAR.** On a standard Borel space with a finite
measure, if the response indicator `ω ↦ ω ∈ R` is conditionally independent of `Y` given `m`
(Mathlib's `CondIndepFun`), then `P(R ∩ {Y ∈ S} | m) = P(R | m) P(Y ∈ S | m)` a.e. for every
measurable `S`: the instance `s = {True}` of `condIndepFun_iff_condExp_inter_preimage_eq_mul`.
For a real outcome this is the MAR hypothesis of `condExp_indicator_ae_eq_mul_of_mar` and
`integral_ipw_eq_integral_of_mar_sigma`; with `m = σ(X)` it applies to
`MissingAtRandomCondIndepFun μ R X hX Y`, which unfolds to this `CondIndepFun`. -/
theorem condExp_inter_preimage_ae_eq_mul_of_condIndepFun [StandardBorelSpace Ω] {𝒴 : Type*}
    [MeasurableSpace 𝒴] (hm : m ≤ mΩ) {R : Set Ω} (hR : MeasurableSet R) {Y : Ω → 𝒴}
    (hY : Measurable Y) (h : CondIndepFun m hm (· ∈ R) Y μ) :
    ∀ S, MeasurableSet S →
      (μ⟦R ∩ Y ⁻¹' S | m⟧) =ᵐ[μ] (μ⟦R | m⟧) * (μ⟦Y ⁻¹' S | m⟧) := by
  intro S hS
  have hpre : (· ∈ R) ⁻¹' ({True} : Set Prop) = R := by
    ext ω; simp
  have key := (condIndepFun_iff_condExp_inter_preimage_eq_mul (measurable_mem_set hR) hY).1 h
    {True} S (measurableSet_singleton _) hS
  rw [hpre] at key
  exact key

omit [IsFiniteMeasure μ] in
/-- For an integrable outcome and strong positivity `P(R | m) ≥ ε > 0` given a sub-σ-algebra `m`
(no MAR assumption is needed), the inverse-response-weighted outcome `1_R Y / P(R | m)` is
integrable. -/
theorem integrable_ipw_condExp_of_pos (hm : m ≤ mΩ) {R : Set Ω} (hR : MeasurableSet R)
    {Y : Ω → ℝ} (hYi : Integrable Y μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ (μ⟦R | m⟧) ω) :
    Integrable (R.indicator fun ω => Y ω / (μ⟦R | m⟧) ω) μ := by
  have heq : (R.indicator fun ω => Y ω / (μ⟦R | m⟧) ω) =
      (fun ω => ((μ⟦R | m⟧) ω)⁻¹) * R.indicator Y := by
    funext ω
    by_cases hω : ω ∈ R <;> simp [hω, div_eq_inv_mul]
  rw [heq]
  refine (hYi.indicator hR).bdd_mul
    ((stronglyMeasurable_condExp.mono hm).measurable.inv.aestronglyMeasurable)
    (c := ε⁻¹) (hpos.mono fun ω hω => ?_)
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans_le hω)]
  exact inv_anti₀ hε hω

omit [IsFiniteMeasure μ] in
/-- **Identification by inverse-response weighting under MAR, general covariate σ-algebra.**
Under a probability law, let `m ≤ mΩ` be the always-observed covariate information and
`π = P(R | m)` the response probability. If the integrable outcome `Y` is missing at random
given `m`, `P(R ∩ {Y ∈ S} | m) = π P(Y ∈ S | m)` a.e. for every measurable `S` (a set-wise
form of the conditional independence `R ⊥ Y | m`), and strong positivity `π ≥ ε > 0` holds
a.e., then the inverse-response-weighted mean `E[1_R Y / π]` (an observed-data estimand) equals
the full-data mean `E[Y]`. Proved by `condExp_indicator_ae_eq_mul_of_mar` and the general
inverse-weighting theorem `integral_ipw_eq_integral_of_mar_condExp`. -/
theorem integral_ipw_eq_integral_of_mar_sigma (hm : m ≤ mΩ) [IsProbabilityMeasure μ]
    {R : Set Ω} (hR : MeasurableSet R) {Y : Ω → ℝ} (hY : Measurable Y)
    (hYi : Integrable Y μ)
    (hMAR : ∀ S, MeasurableSet S →
      (μ⟦R ∩ Y ⁻¹' S | m⟧) =ᵐ[μ] (μ⟦R | m⟧) * (μ⟦Y ⁻¹' S | m⟧))
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε ≤ (μ⟦R | m⟧) ω) :
    ∫ ω, R.indicator (fun ω => Y ω / (μ⟦R | m⟧) ω) ω ∂μ = ∫ ω, Y ω ∂μ :=
  integral_ipw_eq_integral_of_mar_condExp hm hR hYi
    (condExp_indicator_ae_eq_mul_of_mar hm hR hY hYi hMAR) hε hpos

end MARSigma

end MathlibExt.Probability.Causality.MissingData

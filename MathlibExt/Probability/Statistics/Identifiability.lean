/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Probability.Kernel.Basic
public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Estimand identification and the two-point lower bound

A real estimand `τ` is identified by observation laws `P` when parameters with equal laws have
equal estimand values (`IsIdentifiedBy`); this is weaker than injectivity of `θ ↦ P θ`. If two
parameters have the same law but estimand values more than `2ε` apart, no fixed measurable
estimator can be within `ε` of the estimand with probability above `1/2` at both: identification
is necessary for accurate estimation, but it is not itself a statement about any estimator.

## Main definitions

* `IsIdentifiedBy`

## Main results

* `two_point_lower_bound`: the two `ε`-success probabilities sum to at most `1`.
* `exists_measureReal_failure_ge_half`: one failure probability is at least `1/2`.
* `not_isIdentifiedBy_of_eq_of_ne`: equal laws with different estimand values refute
  identification.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Causality

namespace MathlibExt.Probability.Statistics

/-- The real estimand `τ` is *identified* by the family of observation laws `P` if parameters
with equal laws have equal estimand values. This is weaker than injectivity of `θ ↦ P θ`. -/
def IsIdentifiedBy {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X) (τ : Θ → ℝ) : Prop :=
  ∀ θ θ', P θ = P θ' → τ θ = τ θ'

set_option linter.unusedVariables false in
/-- **Two-point indistinguishability.** If two parameters have the same observation law and
estimand values more than `2ε` apart, the `ε`-success events of any fixed measurable estimator
`δ` at the two parameters have total probability at most `1`. -/
theorem two_point_lower_bound {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) {θ θ' : Θ} (hP : P θ = P θ')
    [IsProbabilityMeasure (P θ)] {δ : X → ℝ} (hδ : Measurable δ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : 2 * ε < |τ θ - τ θ'|) :
    (P θ).real {x | |δ x - τ θ| ≤ ε} + (P θ').real {x | |δ x - τ θ'| ≤ ε} ≤ 1 := by
  rw [← hP]
  have hdisj : Disjoint {x | |δ x - τ θ| ≤ ε} {x | |δ x - τ θ'| ≤ ε} :=
    Set.disjoint_left.2 fun x (h1 : |δ x - τ θ| ≤ ε) (h2 : |δ x - τ θ'| ≤ ε) => by
      linarith [abs_sub_le (τ θ) (δ x) (τ θ'), abs_sub_comm (τ θ) (δ x)]
  have hm : MeasurableSet {x | |δ x - τ θ'| ≤ ε} :=
    measurableSet_le (continuous_abs.measurable.comp (hδ.sub_const _)) measurable_const
  rw [← measureReal_union hdisj hm]
  exact measureReal_le_one

/-- **Estimation lower bound from non-identification.** Under the same hypotheses, every fixed
measurable estimator misses the estimand by more than `ε` with probability at least `1/2` at
one of the two parameters. -/
theorem exists_measureReal_failure_ge_half {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) {θ θ' : Θ} (hP : P θ = P θ')
    [IsProbabilityMeasure (P θ)] {δ : X → ℝ} (hδ : Measurable δ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : 2 * ε < |τ θ - τ θ'|) :
    1 / 2 ≤ (P θ).real {x | ε < |δ x - τ θ|} ∨ 1 / 2 ≤ (P θ').real {x | ε < |δ x - τ θ'|} := by
  have h := two_point_lower_bound P τ hP hδ hε hsep
  have hc : ∀ c : ℝ, {x | ε < |δ x - c|} = {x | |δ x - c| ≤ ε}ᶜ := fun c => by
    ext x
    simp [not_le]
  have hm : ∀ c : ℝ, MeasurableSet {x | |δ x - c| ≤ ε} := fun c =>
    measurableSet_le (continuous_abs.measurable.comp (hδ.sub_const _)) measurable_const
  rw [← hP] at h ⊢
  rw [hc, hc, probReal_compl_eq_one_sub (hm _), probReal_compl_eq_one_sub (hm _)]
  by_contra hne
  rw [not_or, not_le, not_le] at hne
  linarith [hne.1, hne.2]

/-- Equal laws with different estimand values refute identification. -/
theorem not_isIdentifiedBy_of_eq_of_ne {Θ X : Type*} [MeasurableSpace X]
    {P : Θ → Measure X} {τ : Θ → ℝ} {θ θ' : Θ} (hP : P θ = P θ') (hτ : τ θ ≠ τ θ') :
    ¬ IsIdentifiedBy P τ := by
  exact fun h => hτ (h θ θ' hP)

/-- **Two-point bound for randomized rules.** Equal observation laws induce equal output
laws under a fixed Markov kernel, so the deterministic disjointness argument applies on
the output space. -/
theorem exists_measureReal_failure_ge_half_kernel {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) {θ θ' : Θ} (hP : P θ = P θ')
    [IsProbabilityMeasure (P θ)] {κ : Kernel X ℝ} [IsMarkovKernel κ]
    {ε : ℝ} (hε : 0 ≤ ε) (hsep : 2 * ε < |τ θ - τ θ'|) :
    1 / 2 ≤ ((P θ).bind κ).real {y | ε < |y - τ θ|} ∨
      1 / 2 ≤ ((P θ').bind κ).real {y | ε < |y - τ θ'|} := by
  have hbind : (P θ).bind κ = (P θ').bind κ := by rw [hP]
  haveI : IsProbabilityMeasure ((P θ).bind κ) := ⟨by
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.measurable κ).aemeasurable]
    have h1 : ∀ a, (κ a : Measure ℝ) Set.univ = 1 :=
      fun a => @measure_univ _ _ _ (IsMarkovKernel.isProbabilityMeasure a)
    simp_rw [h1, lintegral_const, measure_univ, mul_one]
  ⟩
  have hdisj : Disjoint {y | |y - τ θ| ≤ ε} {y | |y - τ θ'| ≤ ε} :=
    Set.disjoint_left.2 fun y (h1 : |y - τ θ| ≤ ε) (h2 : |y - τ θ'| ≤ ε) => by
      linarith [abs_sub_le (τ θ) y (τ θ'), abs_sub_comm (τ θ) y]
  have hm : ∀ c : ℝ, MeasurableSet {y | |y - c| ≤ ε} := fun c =>
    measurableSet_le (continuous_abs.measurable.comp (measurable_id.sub_const _)) measurable_const
  have hsum : ((P θ).bind κ).real {y | |y - τ θ| ≤ ε}
      + ((P θ').bind κ).real {y | |y - τ θ'| ≤ ε} ≤ 1 := by
    rw [← hbind]
    rw [← measureReal_union hdisj (hm _)]
    exact measureReal_le_one
  have hc : ∀ c : ℝ, {y | ε < |y - c|} = {y | |y - c| ≤ ε}ᶜ := fun c => by
    ext y
    simp [not_le]
  rw [← hP] at hsum ⊢
  rw [hc, hc, probReal_compl_eq_one_sub (hm _), probReal_compl_eq_one_sub (hm _)]
  by_contra hne
  rw [not_or, not_le, not_le] at hne
  linarith [hne.1, hne.2]

/-- **Deterministic estimators are the special case.** With `κ := Kernel.deterministic δ`,
the kernel bound is the deterministic bound; the proof is one invocation, not a new
disjointness argument. -/
theorem exists_measureReal_failure_ge_half_of_deterministic {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) {θ θ' : Θ} (hP : P θ = P θ')
    [IsProbabilityMeasure (P θ)] {δ : X → ℝ} (hδ : Measurable δ)
    {ε : ℝ} (hε : 0 ≤ ε) (hsep : 2 * ε < |τ θ - τ θ'|) :
    1 / 2 ≤ ((P θ).bind (Kernel.deterministic δ hδ)).real {y | ε < |y - τ θ|} ∨
      1 / 2 ≤ ((P θ').bind (Kernel.deterministic δ hδ)).real {y | ε < |y - τ θ'|} := by
  haveI := Kernel.isMarkovKernel_deterministic hδ
  exact exists_measureReal_failure_ge_half_kernel (κ := Kernel.deterministic δ hδ)
    P τ hP hε hsep

/-- Observed triple: covariate, treatment indicator (`1` on `T`), observed outcome. -/
noncomputable def obsDatum {Ω : Type*} {𝒳 : Type*} (T : Set Ω) (X : Ω → 𝒳) (Y₀ Y₁ : Ω → ℝ) (ω : Ω) :
    𝒳 × ℝ × ℝ :=
  (X ω, T.indicator 1 ω, observed T Y₀ Y₁ ω)

/-- Observational law: pushforward of `μ` under the observed triple. -/
noncomputable def obsLaw {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure Ω) (T : Set Ω) (X : Ω → 𝒳) (Y₀ Y₁ : Ω → ℝ) :
    Measure (𝒳 × ℝ × ℝ) :=
  μ.map (obsDatum T X Y₀ Y₁)

/-- Propensity read off from an observational law: treated mass over total mass above `w`. -/
noncomputable def propensityFromLaw {𝒳 : Type*} [MeasurableSpace 𝒳] (ν : Measure (𝒳 × ℝ × ℝ)) (w : 𝒳) : ℝ :=
  ν.real ({w} ×ˢ ({1} ×ˢ (Set.univ : Set ℝ))) /
    ν.real ({w} ×ˢ (Set.univ ×ˢ (Set.univ : Set ℝ)))

/-- IPW functional of an observational law: treated term minus control term, with the
law-read propensity in the denominators. -/
noncomputable def ipwATE {𝒳 : Type*} [MeasurableSpace 𝒳] (ν : Measure (𝒳 × ℝ × ℝ)) : ℝ :=
  ∫ s, ((({1} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) s.2) *
      s.2.2 / propensityFromLaw ν s.1 -
    ((({0} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) s.2) *
      s.2.2 / (1 - propensityFromLaw ν s.1))) ∂ν

/-- **IPW identification at one setting.** Under strong ignorability, the ATE equals the
IPW functional of the observational law. -/
theorem ate_eq_ipwATE_obsLaw
    {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [Finite 𝒳] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ}
    (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁)
    (hY₀i : Integrable Y₀ μ) (hY₁i : Integrable Y₁ μ)
    (hSI : StronglyIgnorable μ T (fun ω => (Y₀ ω, Y₁ ω)) X) :
    (∫ ω, (Y₁ ω - Y₀ ω) ∂μ) = ipwATE (obsLaw μ T X Y₀ Y₁) := by
  have hipw := integral_ipw_ate hT hX hY₀ hY₁ hY₀i hY₁i hSI
  have hobsY : Measurable (observed T Y₀ Y₁) := by
    unfold observed
    exact (Measurable.indicator hY₁ hT).add (Measurable.indicator hY₀ hT.compl)
  have h1 : Measurable fun ω : Ω => T.indicator (1 : Ω → ℝ) ω :=
    Measurable.indicator measurable_const hT
  have hobs : Measurable (obsDatum T X Y₀ Y₁) := by
    unfold obsDatum
    exact hX.prodMk (h1.prodMk hobsY)
  have hind : ∀ ω : Ω, T.indicator (1 : Ω → ℝ) ω = 1 ↔ ω ∈ T := by
    intro ω
    by_cases hmem : ω ∈ T
    · simp [hmem]
    · simp [hmem]
  have hpre1 : ∀ w : 𝒳, (obsDatum T X Y₀ Y₁) ⁻¹' ({w} ×ˢ ({1} ×ˢ (Set.univ : Set ℝ))) =
      T ∩ X ⁻¹' {w} := by
    intro w
    ext ω
    unfold obsDatum
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ,
      Set.mem_inter_iff, and_true]
    rw [hind ω]
    tauto
  have hpre2 : ∀ w : 𝒳, (obsDatum T X Y₀ Y₁) ⁻¹' ({w} ×ˢ (Set.univ ×ˢ (Set.univ : Set ℝ))) =
      X ⁻¹' {w} := by
    intro w
    ext ω
    unfold obsDatum
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ]
    tauto
  have hprop : ∀ w : 𝒳, propensityFromLaw (μ.map (obsDatum T X Y₀ Y₁)) w =
      propensity μ T X w := by
    intro w
    have h1 : MeasurableSet ((({w} ×ˢ ({1} ×ˢ (Set.univ : Set ℝ)))) : Set (𝒳 × ℝ × ℝ)) :=
      (measurableSet_singleton w).prod ((measurableSet_singleton 1).prod MeasurableSet.univ)
    have h2 : MeasurableSet ((({w} ×ˢ (Set.univ ×ˢ (Set.univ : Set ℝ)))) : Set (𝒳 × ℝ × ℝ)) :=
      (measurableSet_singleton w).prod (MeasurableSet.univ.prod MeasurableSet.univ)
    unfold propensityFromLaw propensity Measure.real
    rw [Measure.map_apply hobs h1, Measure.map_apply hobs h2, hpre1 w, hpre2 w]
  have hmeasP : Measurable fun w : 𝒳 => propensity μ T X w :=
    fun _ _ => (Set.finite_univ.subset (Set.subset_univ _)).measurableSet
  have hC : Measurable fun s : 𝒳 × ℝ × ℝ =>
      propensityFromLaw (μ.map (obsDatum T X Y₀ Y₁)) s.1 := by
    have heq : (fun s : 𝒳 × ℝ × ℝ => propensityFromLaw (μ.map (obsDatum T X Y₀ Y₁)) s.1) =
        fun s => propensity μ T X s.1 := funext fun s => hprop s.1
    rw [heq]
    exact hmeasP.comp measurable_fst
  have hA1 : Measurable fun s : 𝒳 × ℝ × ℝ =>
      ((({1} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ))) s.2) :=
    (Measurable.indicator measurable_const
      ((measurableSet_singleton (1:ℝ)).prod MeasurableSet.univ)).comp measurable_snd
  have hA0 : Measurable fun s : 𝒳 × ℝ × ℝ =>
      ((({0} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ))) s.2) :=
    (Measurable.indicator measurable_const
      ((measurableSet_singleton (0:ℝ)).prod MeasurableSet.univ)).comp measurable_snd
  have hB : Measurable fun s : 𝒳 × ℝ × ℝ => s.2.2 :=
    measurable_snd.comp measurable_snd
  have hFmeas : AEStronglyMeasurable
      (fun s : 𝒳 × ℝ × ℝ => ((({1} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) s.2) *
        s.2.2 / propensityFromLaw (μ.map (obsDatum T X Y₀ Y₁)) s.1 -
      ((({0} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) s.2) *
        s.2.2 / (1 - propensityFromLaw (μ.map (obsDatum T X Y₀ Y₁)) s.1)))) (μ.map (obsDatum T X Y₀ Y₁)) := by
    apply Measurable.aestronglyMeasurable
    exact ((hA1.mul hB).div hC).sub ((hA0.mul hB).div (measurable_const.sub hC))
  have htrans : ipwATE (obsLaw μ T X Y₀ Y₁) =
      ∫ ω, (T.indicator (fun ω => observed T Y₀ Y₁ ω / propensity μ T X (X ω)) ω -
        Tᶜ.indicator (fun ω => observed T Y₀ Y₁ ω / (1 - propensity μ T X (X ω))) ω) ∂μ := by
    unfold ipwATE obsLaw
    rw [integral_map hobs.aemeasurable hFmeas]
    apply integral_congr_ae
    filter_upwards with ω
    simp only [obsDatum]
    rw [hprop (X ω)]
    by_cases hmem : ω ∈ T
    · have hTcnmem : ω ∉ Tᶜ := fun h => h hmem
      simp only [Set.indicator_of_mem hmem, Set.indicator_of_notMem hTcnmem]
      simp
    · have hTcmem : ω ∈ Tᶜ := hmem
      simp only [Set.indicator_of_notMem hmem, Set.indicator_of_mem hTcmem]
      simp
  rw [htrans]
  exact hipw.symm

/-- **IPW ATE identification through the observational law.** Two settings with equal
observational laws and per-setting strong ignorability have equal ATEs: each ATE equals
the same law-defined IPW functional. -/
theorem ate_isIdentifiedBy_observational_law
    {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [Finite 𝒳] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {Θ : Type*} {μ : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (μ θ)]
    {T : Θ → Set Ω} (hT : ∀ θ, MeasurableSet (T θ))
    {X : Θ → Ω → 𝒳} (hX : ∀ θ, Measurable (X θ))
    {Y₀ Y₁ : Θ → Ω → ℝ}
    (hY₀ : ∀ θ, Measurable (Y₀ θ)) (hY₁ : ∀ θ, Measurable (Y₁ θ))
    (hY₀i : ∀ θ, Integrable (Y₀ θ) (μ θ)) (hY₁i : ∀ θ, Integrable (Y₁ θ) (μ θ))
    (hSI : ∀ θ, StronglyIgnorable (μ θ) (T θ) (fun ω => (Y₀ θ ω, Y₁ θ ω)) (X θ)) :
    IsIdentifiedBy (fun θ => obsLaw (μ θ) (T θ) (X θ) (Y₀ θ) (Y₁ θ))
      (fun θ => ∫ ω, (Y₁ θ ω - Y₀ θ ω) ∂(μ θ)) := by
  intro θ θ' hObs
  show (∫ ω, (Y₁ θ ω - Y₀ θ ω) ∂(μ θ)) = ∫ ω, (Y₁ θ' ω - Y₀ θ' ω) ∂(μ θ')
  have hθ := ate_eq_ipwATE_obsLaw (hT θ) (hX θ) (hY₀ θ) (hY₁ θ) (hY₀i θ) (hY₁i θ) (hSI θ)
  have hθ' := ate_eq_ipwATE_obsLaw (hT θ') (hX θ') (hY₀ θ') (hY₁ θ') (hY₀i θ') (hY₁i θ') (hSI θ')
  have hObs' : obsLaw (μ θ) (T θ) (X θ) (Y₀ θ) (Y₁ θ) =
      obsLaw (μ θ') (T θ') (X θ') (Y₀ θ') (Y₁ θ') := hObs
  rw [hθ, hθ', hObs']

end MathlibExt.Probability.Statistics

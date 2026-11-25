/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Identifiability

import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory

/-!
# The ATE is not identified by the observed law without assumptions

The observed datum sees each potential outcome only on the arm where it
is received: two schedules that agree on `Y₁` over `T` and on `Y₀` over
`Tᶜ` induce the same observed datum and the same observed law
(`obsDatum_eq_of_eqOn`, `obsLaw_eq_of_eqOn`). Counterfactual mass can
therefore be moved between points that are never observed together
without changing anything observable, while changing
`∫ ω, (Y₁ ω - Y₀ ω)` to any prescribed real value, equal or different
(`exists_obsLaw_eq_integral_sub_eq`, `exists_obsLaw_eq_integral_sub_ne`).
Hence neither the integral contrast nor its finite-population special
case, the ATE, is a functional of the observed law
(`not_isIdentifiedBy_obsLaw_integral_sub`, `not_isIdentifiedBy_obsLaw_ate`)
without further assumptions such as strong ignorability.
-/


namespace MathlibExt.Probability.Statistics

open MathlibExt.Probability.Causality

/-- The observed datum depends on the potential outcomes only through the received arm: two
schedules that agree on `Y₁` over `T` and on `Y₀` over `Tᶜ` have the same observed datum at
every point. -/
theorem obsDatum_eq_of_eqOn {Ω 𝒳 : Type*} {T : Set Ω} (X : Ω → 𝒳) {Y₀ Y₁ Y₀' Y₁' : Ω → ℝ}
    (h₁ : Set.EqOn Y₁' Y₁ T) (h₀ : Set.EqOn Y₀' Y₀ Tᶜ) :
    obsDatum T X Y₀' Y₁' = obsDatum T X Y₀ Y₁ := by
  funext ω
  have e : observed T Y₀' Y₁' ω = observed T Y₀ Y₁ ω := by
    simp only [observed, Pi.add_apply]
    by_cases hω : ω ∈ T
    · have hc : ω ∉ Tᶜ := by simpa using hω
      rw [Set.indicator_of_mem hω Y₁', Set.indicator_of_mem hω Y₁,
        Set.indicator_of_notMem hc, Set.indicator_of_notMem hc, h₁ hω]
    · have hc : ω ∈ Tᶜ := (Set.mem_compl_iff T ω).mpr hω
      rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
        Set.indicator_of_mem hc Y₀', Set.indicator_of_mem hc Y₀, h₀ hc]
  simp only [obsDatum]
  rw [e]

/-- **Same observed law, different unobserved potential outcomes.** Changing `Y₀` on the
treated and `Y₁` on the controls leaves the observed-data law unchanged, for every measure. -/
theorem obsLaw_eq_of_eqOn {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    (μ : Measure Ω) {T : Set Ω} (X : Ω → 𝒳) {Y₀ Y₁ Y₀' Y₁' : Ω → ℝ}
    (h₁ : Set.EqOn Y₁' Y₁ T) (h₀ : Set.EqOn Y₀' Y₀ Tᶜ) :
    obsLaw μ T X Y₀' Y₁' = obsLaw μ T X Y₀ Y₁ := by
  simp only [obsLaw, obsDatum_eq_of_eqOn X h₁ h₀]

/-- **The identified set of the ATE is all of `ℝ`.** For every measurable covariate,
every measurable, integrable potential-outcome model and every `t : ℝ` there is a
measurable, integrable model that agrees
with it on the received arm (so has the same observed-data law), has unit effect `t` at every
point, and has ATE `t`. No ignorability, overlap or bounds are assumed; the treated event may
have probability `0` or `1`. -/
theorem exists_obsLaw_eq_integral_sub_eq {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) (X : Ω → 𝒳) (_hX : Measurable X) {Y₀ Y₁ : Ω → ℝ}
    (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁) (hY₀i : Integrable Y₀ μ)
    (hY₁i : Integrable Y₁ μ) (t : ℝ) :
    ∃ Y₀' Y₁' : Ω → ℝ, Measurable Y₀' ∧ Measurable Y₁' ∧ Integrable Y₀' μ ∧
      Integrable Y₁' μ ∧ Set.EqOn Y₁' Y₁ T ∧ Set.EqOn Y₀' Y₀ Tᶜ ∧
      (∀ ω, Y₁' ω - Y₀' ω = t) ∧ obsLaw μ T X Y₀' Y₁' = obsLaw μ T X Y₀ Y₁ ∧
      ∫ ω, (Y₁' ω - Y₀' ω) ∂μ = t := by
  refine ⟨T.indicator (fun ω => Y₁ ω - t) + Tᶜ.indicator Y₀,
    T.indicator Y₁ + Tᶜ.indicator (fun ω => Y₀ ω + t),
    ((hY₁.sub measurable_const).indicator hT).add (hY₀.indicator hT.compl),
    (hY₁.indicator hT).add ((hY₀.add measurable_const).indicator hT.compl),
    ((hY₁i.sub (integrable_const t)).indicator hT).add (hY₀i.indicator hT.compl),
    ((hY₁i.indicator hT).add ((hY₀i.add (integrable_const t)).indicator hT.compl)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro ω hω
    have hc : ω ∉ Tᶜ := by simpa using hω
    simp only [Pi.add_apply, Set.indicator_of_mem hω Y₁,
      Set.indicator_of_notMem hc, add_zero]
  · intro ω hω
    have hn : ω ∉ T := (Set.mem_compl_iff T ω).mp hω
    simp only [Pi.add_apply, Set.indicator_of_notMem hn,
      Set.indicator_of_mem hω Y₀, zero_add]
  · intro ω
    simp only [Pi.add_apply]
    by_cases hω : ω ∈ T
    · have hc : ω ∉ Tᶜ := by simpa using hω
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω,
        Set.indicator_of_notMem hc, Set.indicator_of_notMem hc]
      ring
    · have hc : ω ∈ Tᶜ := (Set.mem_compl_iff T ω).mpr hω
      rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
        Set.indicator_of_mem hc, Set.indicator_of_mem hc]
      ring
  · apply obsLaw_eq_of_eqOn
    · intro ω hω
      have hc : ω ∉ Tᶜ := by simpa using hω
      simp only [Pi.add_apply, Set.indicator_of_mem hω Y₁,
        Set.indicator_of_notMem hc, add_zero]
    · intro ω hω
      have hn : ω ∉ T := (Set.mem_compl_iff T ω).mp hω
      simp only [Pi.add_apply, Set.indicator_of_notMem hn,
        Set.indicator_of_mem hω Y₀, zero_add]
  · have hfun : (fun ω => (T.indicator Y₁ + Tᶜ.indicator (fun ω => Y₀ ω + t)) ω -
      (T.indicator (fun ω => Y₁ ω - t) + Tᶜ.indicator Y₀) ω) = fun _ => t := by
      funext ω
      simp only [Pi.add_apply]
      by_cases hω : ω ∈ T
      · have hc : ω ∉ Tᶜ := by simpa using hω
        rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω,
          Set.indicator_of_notMem hc, Set.indicator_of_notMem hc]
        ring
      · have hc : ω ∈ Tᶜ := (Set.mem_compl_iff T ω).mpr hω
        rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
          Set.indicator_of_mem hc, Set.indicator_of_mem hc]
        ring
    rw [hfun, integral_const, probReal_univ, one_smul]

/-- **No functional of the observed law recovers the ATE at any model.** For every
measurable covariate, every measurable, integrable model and every `F`, some
measurable, integrable model with the same
observed-data law has ATE different from `F` of that law. -/
theorem exists_obsLaw_eq_integral_sub_ne {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒳] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) (X : Ω → 𝒳) (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ}
    (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁) (hY₀i : Integrable Y₀ μ)
    (hY₁i : Integrable Y₁ μ)
    (F : Measure (𝒳 × ℝ × ℝ) → ℝ) :
    ∃ Y₀' Y₁' : Ω → ℝ, Measurable Y₀' ∧ Measurable Y₁' ∧ Integrable Y₀' μ ∧
      Integrable Y₁' μ ∧ obsLaw μ T X Y₀' Y₁' = obsLaw μ T X Y₀ Y₁ ∧
      F (obsLaw μ T X Y₀' Y₁') ≠ ∫ ω, (Y₁' ω - Y₀' ω) ∂μ := by
  obtain ⟨Y₀', Y₁', m0, m1, i0, i1, _, _, _, hobs, hint⟩ :=
    exists_obsLaw_eq_integral_sub_eq (μ := μ) hT X hX hY₀ hY₁ hY₀i hY₁i
      (F (obsLaw μ T X Y₀ Y₁) + 1)
  exact ⟨Y₀', Y₁', m0, m1, i0, i1, hobs, by rw [hobs, hint]; exact (lt_add_one _).ne⟩

/-- **The ATE is not identified without extra assumptions.** For every probability space,
every measurable treated event `T` and every measurable covariate `X`, the
observed-data law does not
identify the ATE on the class of measurable, integrable potential-outcome schedules. -/
theorem not_isIdentifiedBy_obsLaw_integral_sub {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒳] (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) (X : Ω → 𝒳) (hX : Measurable X) :
    ¬ IsIdentifiedBy
      (fun θ : {θ : (Ω → ℝ) × (Ω → ℝ) //
          Measurable θ.1 ∧ Measurable θ.2 ∧ Integrable θ.1 μ ∧ Integrable θ.2 μ} =>
        obsLaw μ T X θ.1.1 θ.1.2)
      (fun θ => ∫ ω, (θ.1.2 ω - θ.1.1 ω) ∂μ) := by
  obtain ⟨Y₀a, Y₁a, m0a, m1a, i0a, i1a, _, _, _, hobsa, hinta⟩ :=
    exists_obsLaw_eq_integral_sub_eq (μ := μ) hT X hX (Y₀ := 0) (Y₁ := 0)
      measurable_const measurable_const (integrable_const 0) (integrable_const 0) 0
  obtain ⟨Y₀b, Y₁b, m0b, m1b, i0b, i1b, _, _, _, hobsb, hintb⟩ :=
    exists_obsLaw_eq_integral_sub_eq (μ := μ) hT X hX (Y₀ := 0) (Y₁ := 0)
      measurable_const measurable_const (integrable_const 0) (integrable_const 0) 1
  refine not_isIdentifiedBy_of_eq_of_ne (θ := ⟨(Y₀a, Y₁a), m0a, m1a, i0a, i1a⟩)
    (θ' := ⟨(Y₀b, Y₁b), m0b, m1b, i0b, i1b⟩) ?_ ?_
  · show obsLaw μ T X Y₀a Y₁a = obsLaw μ T X Y₀b Y₁b
    rw [hobsa, hobsb]
  · show (∫ ω, (Y₁a ω - Y₀a ω) ∂μ) ≠ ∫ ω, (Y₁b ω - Y₀b ω) ∂μ
    rw [hinta, hintb]
    norm_num

/-- **Finite population: the ATE is not identified.** For a nonempty finite population
with measurable singletons, every measure on the units, every treated set and every
covariate, the observed-data law does not
identify the finite-population ATE `ate y₀ y₁`. -/
theorem not_isIdentifiedBy_obsLaw_ate {ι 𝒳 : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace 𝒳]
    (μ : Measure ι) (T : Set ι) (X : ι → 𝒳) :
    ¬ IsIdentifiedBy (fun θ : (ι → ℝ) × (ι → ℝ) => obsLaw μ T X θ.1 θ.2)
      (fun θ => ate θ.1 θ.2) := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := ι))
  have hsum1 : (∑ i, (if i = i₀ then (1 : ℝ) else 0)) = 1 := by simp
  by_cases hi₀ : i₀ ∈ T
  · have hP : obsLaw μ T X (fun i => if i = i₀ then (1 : ℝ) else 0) 0
        = obsLaw μ T X 0 0 := by
      apply obsLaw_eq_of_eqOn
      · intro ω _
        rfl
      · intro ω hω
        have hne : ω ≠ i₀ := fun heq => ((Set.mem_compl_iff T ω).mp hω) (heq.symm ▸ hi₀)
        show (if ω = i₀ then (1 : ℝ) else 0) = 0
        simp [hne]
    have hτ : ate (fun i => if i = i₀ then (1 : ℝ) else 0) (0 : ι → ℝ)
        ≠ ate (0 : ι → ℝ) 0 := by
      have hsum : (∑ i, ((0 : ι → ℝ) i - (if i = i₀ then (1 : ℝ) else 0))) = -1 := by
        simp only [Pi.zero_apply]
        rw [Finset.sum_sub_distrib, Finset.sum_const_zero, hsum1, zero_sub]
      have hrhs : (∑ i, ((0 : ι → ℝ) i - (0 : ι → ℝ) i)) = 0 := by simp
      simp only [ate, popMean, hsum, hrhs, zero_div]
      exact div_ne_zero (by norm_num) hc
    exact not_isIdentifiedBy_of_eq_of_ne
      (θ := ((fun i => if i = i₀ then (1 : ℝ) else 0), 0)) (θ' := (0, 0)) hP hτ
  · have hP : obsLaw μ T X 0 (fun i => if i = i₀ then (1 : ℝ) else 0)
        = obsLaw μ T X 0 0 := by
      apply obsLaw_eq_of_eqOn
      · intro ω hω
        have hne : ω ≠ i₀ := fun heq => hi₀ (heq ▸ hω)
        show (if ω = i₀ then (1 : ℝ) else 0) = 0
        simp [hne]
      · intro ω _
        rfl
    have hτ : ate (0 : ι → ℝ) (fun i => if i = i₀ then (1 : ℝ) else 0)
        ≠ ate (0 : ι → ℝ) 0 := by
      have hsum : (∑ i, ((if i = i₀ then (1 : ℝ) else 0) - (0 : ι → ℝ) i)) = 1 := by
        simp only [Pi.zero_apply, sub_zero, hsum1]
      have hrhs : (∑ i, ((0 : ι → ℝ) i - (0 : ι → ℝ) i)) = 0 := by simp
      simp only [ate, popMean, hsum, hrhs, zero_div]
      exact div_ne_zero one_ne_zero hc
    exact not_isIdentifiedBy_of_eq_of_ne
      (θ := (0, (fun i => if i = i₀ then (1 : ℝ) else 0))) (θ' := (0, 0)) hP hτ

end MathlibExt.Probability.Statistics

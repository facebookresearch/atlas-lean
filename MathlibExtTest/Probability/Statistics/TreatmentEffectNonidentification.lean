/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.TreatmentEffectNonidentification

import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory


namespace MathlibExtTest.Probability.Statistics.TreatmentEffectNonidentification

open MathlibExt.Probability.Causality MathlibExt.Probability.Statistics

/-- A fair coin on `Bool`: two units, or a treatment coin. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp [fairCoin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The treated unit. -/
abbrev treated : Set Bool := {true}

/-- No covariate. -/
abbrev noCov : Bool → Unit := fun _ => ()

/-- Second model: untreated outcome `-1` on the treated unit, treated outcome `1` on the
control unit, `0` on every received arm. -/
noncomputable abbrev y0B : Bool → ℝ := fun ω => -treated.indicator (fun _ => (1 : ℝ)) ω

/-- See `y0B`. -/
noncomputable abbrev y1B : Bool → ℝ := fun ω => treatedᶜ.indicator (fun _ => (1 : ℝ)) ω

/-- Two finite models, observed law: the all-zero model and `(y0B, y1B)` agree on every
received arm, so they have the same observed-data law. -/
theorem two_finite_models_obsLaw_eq :
    obsLaw fairCoin treated noCov y0B y1B = obsLaw fairCoin treated noCov 0 0 := by
  apply obsLaw_eq_of_eqOn
  · intro ω hω
    simp only [Set.mem_singleton_iff] at hω
    subst hω
    simp
  · intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hω
    simp [hω]

/-- Two finite models, different ATEs and nonidentification: the two finite models have
finite-population ATEs `1` and `0`, so the observed law does not identify the ATE. -/
theorem two_finite_models_not_identified :
    ate y0B y1B ≠ ate (0 : Bool → ℝ) 0 ∧
      ¬ IsIdentifiedBy (fun θ : (Bool → ℝ) × (Bool → ℝ) => obsLaw fairCoin treated noCov θ.1 θ.2)
        (fun θ => ate θ.1 θ.2) := by
  refine ⟨?_, not_isIdentifiedBy_of_eq_of_ne (θ := (y0B, y1B)) (θ' := (0, 0))
    two_finite_models_obsLaw_eq ?_⟩ <;>
  · simp [ate, popMean]

/-- The finite-population theorem on the two-unit design. -/
theorem two_unit_design_not_identified :
    ¬ IsIdentifiedBy (fun θ : (Bool → ℝ) × (Bool → ℝ) => obsLaw fairCoin treated noCov θ.1 θ.2)
      (fun θ => ate θ.1 θ.2) :=
  not_isIdentifiedBy_obsLaw_ate fairCoin treated noCov

/-- The measure-theoretic theorem on the two-unit design (measurable, integrable schedules). -/
theorem two_unit_design_not_identified_integral :
    ¬ IsIdentifiedBy
      (fun θ : {θ : (Bool → ℝ) × (Bool → ℝ) //
          Measurable θ.1 ∧ Measurable θ.2 ∧ Integrable θ.1 fairCoin ∧ Integrable θ.2 fairCoin} =>
        obsLaw fairCoin treated noCov θ.1.1 θ.1.2)
      (fun θ => ∫ ω, (θ.1.2 ω - θ.1.1 ω) ∂fairCoin) :=
  not_isIdentifiedBy_obsLaw_integral_sub fairCoin (measurableSet_singleton true) noCov

/-- Identification boundary: the two observationally equivalent models cannot both be
strongly ignorable, else the upstream identification theorem would equate their ATEs. -/
theorem two_finite_models_not_both_stronglyIgnorable :
    ¬ (StronglyIgnorable fairCoin treated (fun _ => ((0 : ℝ), (0 : ℝ))) noCov ∧
      StronglyIgnorable fairCoin treated (fun ω => (y0B ω, y1B ω)) noCov) := by
  rintro ⟨hA, hB⟩
  have hId := ate_isIdentifiedBy_observational_law (Θ := Bool) (μ := fun _ => fairCoin)
    (T := fun _ => treated) (X := fun _ => noCov)
    (Y₀ := fun b => if b then y0B else 0) (Y₁ := fun b => if b then y1B else 0)
    (fun _ => measurableSet_singleton true) (fun _ => measurable_const)
    (fun _ => Measurable.of_discrete) (fun _ => Measurable.of_discrete)
    (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite)
    (fun b => by
      cases b with
      | false => exact hA
      | true => exact hB) true false two_finite_models_obsLaw_eq
  have hEq : ∫ ω, (y1B ω - y0B ω) ∂fairCoin = ∫ ω, ((0 : ℝ) - 0) ∂fairCoin := hId
  have h1 : (fun ω => y1B ω - y0B ω) = fun _ => (1 : ℝ) := by
    funext ω
    cases ω <;> simp
  rw [h1, integral_const, probReal_univ, one_smul, sub_self, integral_zero] at hEq
  norm_num at hEq

/-- Consistency is the only link between outcomes and data: in the all-treated population the
observed datum (covariate, treatment indicator, observed outcome) is the same at every point
whatever `Y₀` is. -/
theorem allTreated_obsDatum_eq (Y₀ Y₀' Y₁ : Bool → ℝ) :
    obsDatum Set.univ noCov Y₀' Y₁ = obsDatum Set.univ noCov Y₀ Y₁ :=
  obsDatum_eq_of_eqOn noCov (fun _ _ => rfl) fun ω hω => absurd (Set.mem_univ ω) hω

/-- All-treated population: the observed law does not depend on `Y₀` at all. -/
theorem allTreated_obsLaw_eq (Y₀ Y₀' Y₁ : Bool → ℝ) :
    obsLaw fairCoin Set.univ noCov Y₀' Y₁ = obsLaw fairCoin Set.univ noCov Y₀ Y₁ :=
  obsLaw_eq_of_eqOn fairCoin noCov (fun _ _ => rfl) fun ω hω => absurd (Set.mem_univ ω) hω

/-- All-treated population: treatment is conditionally independent of every outcome, yet
overlap fails, so the population is not strongly ignorable. -/
theorem allTreated_condIndep_not_stronglyIgnorable (V : Bool → ℝ × ℝ) :
    CondIndepDiscrete fairCoin Set.univ V noCov ∧
      ¬ StronglyIgnorable fairCoin Set.univ V noCov := by
  refine ⟨fun B _ w => by simp only [Set.univ_inter, mul_comm], fun h => ?_⟩
  have hpre : noCov ⁻¹' {()} = Set.univ := Set.eq_univ_of_forall fun _ => rfl
  have hw : fairCoin (noCov ⁻¹' {()}) ≠ 0 := by
    rw [hpre, measure_univ]
    exact one_ne_zero
  have hlt := (h.2 () hw).2
  rw [propensity, hpre, Set.univ_inter, probReal_univ, div_one] at hlt
  exact lt_irrefl _ hlt

/-- All-treated population: every real number is the ATE of a model with the observed law of
the all-zero model, so conditional independence without overlap does not identify. -/
theorem allTreated_identified_set (t : ℝ) :
    ∃ Y₀' Y₁' : Bool → ℝ,
      obsLaw fairCoin Set.univ noCov Y₀' Y₁' = obsLaw fairCoin Set.univ noCov 0 0 ∧
        ∫ ω, (Y₁' ω - Y₀' ω) ∂fairCoin = t := by
  obtain ⟨Y₀', Y₁', -, -, -, -, -, -, -, hobs, hint⟩ :=
    exists_obsLaw_eq_integral_sub_eq (μ := fairCoin) MeasurableSet.univ noCov
      (Y₀ := 0) (Y₁ := 0) measurable_const measurable_const (integrable_const 0)
      (integrable_const 0) t
  exact ⟨Y₀', Y₁', hobs, hint⟩

/-- Omitted denominator: in the all-treated population the IPW functional divides its control
term by `1 - 1 = 0`; it is a functional of the observed law, so it misses the ATE at some
model with the same observed law. -/
theorem allTreated_ipwATE_ne :
    ∃ Y₀' Y₁' : Bool → ℝ,
      obsLaw fairCoin Set.univ noCov Y₀' Y₁' = obsLaw fairCoin Set.univ noCov 0 0 ∧
        ipwATE (obsLaw fairCoin Set.univ noCov Y₀' Y₁') ≠ ∫ ω, (Y₁' ω - Y₀' ω) ∂fairCoin := by
  obtain ⟨Y₀', Y₁', -, -, -, -, hobs, hne⟩ :=
    exists_obsLaw_eq_integral_sub_ne (μ := fairCoin) MeasurableSet.univ noCov
      (Y₀ := 0) (Y₁ := 0) measurable_const measurable_const (integrable_const 0)
      (integrable_const 0) ipwATE
  exact ⟨Y₀', Y₁', hobs, hne⟩

/-- Randomized design on `Bool × Bool`: the first coin is the response type, the second the
treatment. -/
noncomputable abbrev coin2 : Measure (Bool × Bool) := fairCoin.prod fairCoin

/-- Treatment: the second coin. -/
abbrev treated2 : Set (Bool × Bool) := {ω | ω.2 = true}

/-- Switching response types: `Y₀` is the type, `Y₁` its negation (unit effects `±1`). -/
noncomputable abbrev sw0 : Bool × Bool → ℝ := fun ω => if ω.1 then 1 else 0

/-- See `sw0`. -/
noncomputable abbrev sw1 : Bool × Bool → ℝ := fun ω => if ω.1 then 0 else 1

/-- Individual effects are not identified from the outcome laws: under randomization, the
switching model and a model with the same observed law (which carries both arm outcome laws)
have the same ATE, yet their unit effects differ at some point. -/
theorem individual_effects_not_identified :
    ∃ Y₀' Y₁' : Bool × Bool → ℝ,
      obsLaw coin2 treated2 (fun _ => ()) Y₀' Y₁' = obsLaw coin2 treated2 (fun _ => ()) sw0 sw1 ∧
      ∫ ω, (Y₁' ω - Y₀' ω) ∂coin2 = ∫ ω, (sw1 ω - sw0 ω) ∂coin2 ∧
      ∃ ω, Y₁' ω - Y₀' ω ≠ sw1 ω - sw0 ω := by
  obtain ⟨Y₀', Y₁', -, -, -, -, -, -, heff, hobs, hint⟩ :=
    exists_obsLaw_eq_integral_sub_eq (μ := coin2) (T := treated2)
      (measurable_snd (measurableSet_singleton true)) (fun _ => ()) (Y₀ := sw0) (Y₁ := sw1)
      Measurable.of_discrete Measurable.of_discrete Integrable.of_finite Integrable.of_finite
      (∫ ω, (sw1 ω - sw0 ω) ∂coin2)
  refine ⟨Y₀', Y₁', hobs, hint, ?_⟩
  by_cases ht : ∫ ω, (sw1 ω - sw0 ω) ∂coin2 = -1
  · refine ⟨(false, true), ?_⟩
    rw [heff, ht]
    norm_num [sw0, sw1]
  · refine ⟨(true, true), ?_⟩
    rw [heff]
    simpa [sw0, sw1] using ht

/-- Zero-mass boundary: under the zero measure every ATE is `0`, so the ATE is identified;
the probability hypothesis of `not_isIdentifiedBy_obsLaw_integral_sub` is needed. -/
theorem zeroMeasure_isIdentifiedBy :
    IsIdentifiedBy
      (fun θ : (Bool → ℝ) × (Bool → ℝ) => obsLaw (0 : Measure Bool) treated noCov θ.1 θ.2)
      (fun θ => ∫ ω, (θ.2 ω - θ.1 ω) ∂(0 : Measure Bool)) :=
  fun _ _ _ => by simp

/-- Omitted denominator, empty population: `ate` divides by `card ι = 0`, so every ATE is `0`
and the ATE is identified; the `Nonempty` hypothesis of `not_isIdentifiedBy_obsLaw_ate` is
needed. -/
theorem emptyPopulation_isIdentifiedBy (μ : Measure (Fin 0)) (T : Set (Fin 0)) :
    IsIdentifiedBy (fun θ : (Fin 0 → ℝ) × (Fin 0 → ℝ) => obsLaw μ T (fun _ => ()) θ.1 θ.2)
      (fun θ => ate θ.1 θ.2) :=
  fun _ _ _ => by simp [ate, popMean]

end MathlibExtTest.Probability.Statistics.TreatmentEffectNonidentification


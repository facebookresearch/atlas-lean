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
    measurable_const

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
    exists_obsLaw_eq_integral_sub_eq (μ := fairCoin) MeasurableSet.univ noCov measurable_const
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
    exists_obsLaw_eq_integral_sub_ne (μ := fairCoin) MeasurableSet.univ noCov measurable_const
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

theorem coin2_fairCoin_true : fairCoin.real {true} = 1 / 2 := by
  simp [fairCoin, Measure.real_def, Measure.smul_apply, Measure.add_apply]

theorem coin2_fairCoin_univ : fairCoin.real Set.univ = 1 := probReal_univ

theorem coin2_real_prod (s : Set Bool) (t : Set Bool) :
    coin2.real (s ×ˢ t) = fairCoin.real s * fairCoin.real t := by
  simp [coin2, Measure.prod_prod, Measure.real_def, ENNReal.toReal_mul]

theorem coin2_treated2_eq : treated2 = Set.univ ×ˢ ({true} : Set Bool) := by
  ext ω
  simp [treated2]

theorem coin2_const_preimage (w : Unit) : (fun _ : Bool × Bool => ()) ⁻¹' {w} = Set.univ := by
  have hw : w = () := Subsingleton.elim _ _
  subst hw
  simp

theorem coin2_vpreimage (B : Set (ℝ × ℝ)) :
    (fun ω : Bool × Bool => (sw0 ω, sw1 ω)) ⁻¹' B =
      {b : Bool | ((if b then (1 : ℝ) else 0, if b then (0 : ℝ) else 1)) ∈ B} ×ˢ Set.univ := by
  ext ω
  simp [sw0, sw1]

theorem coin2_vpreimage_swap (B : Set (ℝ × ℝ)) :
    (fun ω : Bool × Bool => (sw1 ω, sw0 ω)) ⁻¹' B =
      {b : Bool | ((if b then (0 : ℝ) else 1, if b then (1 : ℝ) else 0)) ∈ B} ×ˢ Set.univ := by
  ext ω
  simp [sw0, sw1]

theorem coin2_univ_prob : coin2.real Set.univ = 1 := probReal_univ

theorem coin2_condIndep_sw : CondIndepDiscrete coin2 treated2 (fun ω : Bool × Bool => (sw0 ω, sw1 ω)) (fun _ => ()) := by
  intro B _ w
  rw [coin2_const_preimage w, coin2_treated2_eq, coin2_vpreimage B]
  have h1 : ((Set.univ : Set Bool) ×ˢ ({true} : Set Bool)) ∩ ({b : Bool | ((if b then (1 : ℝ) else 0, if b then (0 : ℝ) else 1)) ∈ B} ×ˢ (Set.univ : Set Bool)) ∩ (Set.univ : Set (Bool × Bool)) =
      {b : Bool | ((if b then (1 : ℝ) else 0, if b then (0 : ℝ) else 1)) ∈ B} ×ˢ ({true} : Set Bool) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  have h2 : ({b : Bool | ((if b then (1 : ℝ) else 0, if b then (0 : ℝ) else 1)) ∈ B} ×ˢ (Set.univ : Set Bool)) ∩ (Set.univ : Set (Bool × Bool)) =
      {b : Bool | ((if b then (1 : ℝ) else 0, if b then (0 : ℝ) else 1)) ∈ B} ×ˢ (Set.univ : Set Bool) := by
    simp
  have h3 : ((Set.univ : Set Bool) ×ˢ ({true} : Set Bool)) ∩ (Set.univ : Set (Bool × Bool)) = (Set.univ : Set Bool) ×ˢ ({true} : Set Bool) := by
    simp
  rw [h1, h2, h3, coin2_univ_prob]
  rw [coin2_real_prod, coin2_real_prod, coin2_real_prod]
  rw [coin2_fairCoin_univ, coin2_fairCoin_true]
  ring

theorem coin2_condIndep_swap : CondIndepDiscrete coin2 treated2 (fun ω : Bool × Bool => (sw1 ω, sw0 ω)) (fun _ => ()) := by
  intro B _ w
  rw [coin2_const_preimage w, coin2_treated2_eq, coin2_vpreimage_swap B]
  have h1 : ((Set.univ : Set Bool) ×ˢ ({true} : Set Bool)) ∩ ({b : Bool | ((if b then (0 : ℝ) else 1, if b then (1 : ℝ) else 0)) ∈ B} ×ˢ (Set.univ : Set Bool)) ∩ (Set.univ : Set (Bool × Bool)) =
      {b : Bool | ((if b then (0 : ℝ) else 1, if b then (1 : ℝ) else 0)) ∈ B} ×ˢ ({true} : Set Bool) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  have h2 : ({b : Bool | ((if b then (0 : ℝ) else 1, if b then (1 : ℝ) else 0)) ∈ B} ×ˢ (Set.univ : Set Bool)) ∩ (Set.univ : Set (Bool × Bool)) =
      {b : Bool | ((if b then (0 : ℝ) else 1, if b then (1 : ℝ) else 0)) ∈ B} ×ˢ (Set.univ : Set Bool) := by
    simp
  have h3 : ((Set.univ : Set Bool) ×ˢ ({true} : Set Bool)) ∩ (Set.univ : Set (Bool × Bool)) = (Set.univ : Set Bool) ×ˢ ({true} : Set Bool) := by
    simp
  rw [h1, h2, h3, coin2_univ_prob]
  rw [coin2_real_prod, coin2_real_prod, coin2_real_prod]
  rw [coin2_fairCoin_univ, coin2_fairCoin_true]
  ring

theorem coin2_overlap (w : Unit) (_ : coin2 ((fun _ : Bool × Bool => ()) ⁻¹' {w}) ≠ 0) :
    0 < propensity coin2 treated2 (fun _ : Bool × Bool => ()) w ∧
    propensity coin2 treated2 (fun _ : Bool × Bool => ()) w < 1 := by
  have hpre := coin2_const_preimage w
  have hT : treated2 ∩ (Set.univ : Set (Bool × Bool)) = (Set.univ : Set Bool) ×ˢ ({true} : Set Bool) := by
    rw [coin2_treated2_eq, Set.inter_univ]
  have hprop : propensity coin2 treated2 (fun _ : Bool × Bool => ()) w = 1 / 2 := by
    simp only [propensity, hpre, hT]
    rw [coin2_real_prod, coin2_univ_prob, coin2_fairCoin_univ, coin2_fairCoin_true, one_mul, div_one]
  rw [hprop]
  norm_num

theorem coin2_eq_dirac : coin2 = (2 : ENNReal)⁻¹ • ((2 : ENNReal)⁻¹ •
    (Measure.dirac (true, true) + Measure.dirac (true, false) +
     Measure.dirac (false, true) + Measure.dirac (false, false))) := by
  simp only [coin2, fairCoin, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.add_prod, Measure.prod_add, Measure.dirac_prod_dirac, smul_add]
  ac_rfl

theorem coin2_integral_sw : ∫ ω, (sw1 ω - sw0 ω) ∂coin2 = 0 := by
  rw [coin2_eq_dirac, integral_smul_measure, integral_smul_measure]
  rw [integral_add_measure Integrable.of_finite Integrable.of_finite,
      integral_add_measure Integrable.of_finite Integrable.of_finite,
      integral_add_measure Integrable.of_finite Integrable.of_finite]
  rw [integral_dirac, integral_dirac, integral_dirac, integral_dirac]
  simp [sw0, sw1]

theorem coin2_integral_swap : ∫ ω, (sw0 ω - sw1 ω) ∂coin2 = 0 := by
  rw [coin2_eq_dirac, integral_smul_measure, integral_smul_measure]
  rw [integral_add_measure Integrable.of_finite Integrable.of_finite,
      integral_add_measure Integrable.of_finite Integrable.of_finite,
      integral_add_measure Integrable.of_finite Integrable.of_finite]
  rw [integral_dirac, integral_dirac, integral_dirac, integral_dirac]
  simp [sw0, sw1]

theorem coin2_obsDatum_f_TT : obsDatum treated2 (fun _ : Bool × Bool => ()) sw0 sw1 (true, true) = ((), 1, 0) := by
  simp [obsDatum, treated2, observed, sw1]

theorem coin2_obsDatum_f_TF : obsDatum treated2 (fun _ : Bool × Bool => ()) sw0 sw1 (true, false) = ((), 0, 1) := by
  simp [obsDatum, treated2, observed, sw0]

theorem coin2_obsDatum_f_FT : obsDatum treated2 (fun _ : Bool × Bool => ()) sw0 sw1 (false, true) = ((), 1, 1) := by
  simp [obsDatum, treated2, observed, sw1]

theorem coin2_obsDatum_f_FF : obsDatum treated2 (fun _ : Bool × Bool => ()) sw0 sw1 (false, false) = ((), 0, 0) := by
  simp [obsDatum, treated2, observed, sw0]

theorem coin2_obsDatum_g_TT : obsDatum treated2 (fun _ : Bool × Bool => ()) sw1 sw0 (true, true) = ((), 1, 1) := by
  simp [obsDatum, treated2, observed, sw0]

theorem coin2_obsDatum_g_TF : obsDatum treated2 (fun _ : Bool × Bool => ()) sw1 sw0 (true, false) = ((), 0, 0) := by
  simp [obsDatum, treated2, observed, sw1]

theorem coin2_obsDatum_g_FT : obsDatum treated2 (fun _ : Bool × Bool => ()) sw1 sw0 (false, true) = ((), 1, 0) := by
  simp [obsDatum, treated2, observed, sw0]

theorem coin2_obsDatum_g_FF : obsDatum treated2 (fun _ : Bool × Bool => ()) sw1 sw0 (false, false) = ((), 0, 1) := by
  simp [obsDatum, treated2, observed, sw1]

theorem coin2_obsLaw_eq :
    obsLaw coin2 treated2 (fun _ : Bool × Bool => ()) sw1 sw0 =
    obsLaw coin2 treated2 (fun _ : Bool × Bool => ()) sw0 sw1 := by
  have hfm : Measurable (obsDatum treated2 (fun _ : Bool × Bool => ()) sw0 sw1) :=
    Measurable.of_discrete
  have hgm : Measurable (obsDatum treated2 (fun _ : Bool × Bool => ()) sw1 sw0) :=
    Measurable.of_discrete
  simp only [obsLaw, coin2_eq_dirac]
  rw [Measure.map_smul _ hgm.aemeasurable, Measure.map_smul _ hgm.aemeasurable,
      Measure.map_smul _ hfm.aemeasurable, Measure.map_smul _ hfm.aemeasurable]
  rw [Measure.map_add _ _ hgm, Measure.map_add _ _ hgm, Measure.map_add _ _ hgm,
      Measure.map_add _ _ hfm, Measure.map_add _ _ hfm, Measure.map_add _ _ hfm]
  rw [Measure.map_dirac, Measure.map_dirac, Measure.map_dirac, Measure.map_dirac,
      Measure.map_dirac, Measure.map_dirac, Measure.map_dirac, Measure.map_dirac]
  rw [coin2_obsDatum_g_TT, coin2_obsDatum_g_TF, coin2_obsDatum_g_FT, coin2_obsDatum_g_FF,
      coin2_obsDatum_f_TT, coin2_obsDatum_f_TF, coin2_obsDatum_f_FT, coin2_obsDatum_f_FF]
  ac_rfl

/-- Individual effects are not identified even under randomization: in the two-coin
randomized design, the switching-response model and the label-swapped model are both
strongly ignorable, have the same observed law and the same ATE, yet their unit effects
differ at some point. -/
theorem individual_effects_not_identified :
    ∃ Y₀' Y₁' : Bool × Bool → ℝ,
      obsLaw coin2 treated2 (fun _ => ()) Y₀' Y₁' = obsLaw coin2 treated2 (fun _ => ()) sw0 sw1 ∧
      ∫ ω, (Y₁' ω - Y₀' ω) ∂coin2 = ∫ ω, (sw1 ω - sw0 ω) ∂coin2 ∧
      (∃ ω, Y₁' ω - Y₀' ω ≠ sw1 ω - sw0 ω) ∧
      StronglyIgnorable coin2 treated2 (fun ω => (sw0 ω, sw1 ω)) (fun _ => ()) ∧
      StronglyIgnorable coin2 treated2 (fun ω => (Y₀' ω, Y₁' ω)) (fun _ => ()) := by
  refine ⟨sw1, sw0, coin2_obsLaw_eq, ?hate, ?hdiff, ⟨coin2_condIndep_sw, coin2_overlap⟩, ⟨coin2_condIndep_swap, coin2_overlap⟩⟩
  · rw [coin2_integral_swap, coin2_integral_sw]
  · exact ⟨(true, true), by norm_num [sw0, sw1]⟩

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

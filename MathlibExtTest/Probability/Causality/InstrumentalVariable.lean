/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.InstrumentalVariable
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic

@[expose] public section

namespace MathlibExtTest.Probability.Causality.InstrumentalVariable

open MathlibExt.Biology.StatisticalGenetics.MendelianRandomization
open MathlibExt.Probability.Causality
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The uniform law on `Bool`. -/
noncomputable def μ2 : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

theorem μ2_singleton (b : Bool) : μ2 {b} = 2⁻¹ := by
  cases b <;> simp [μ2]

instance : IsProbabilityMeasure μ2 := ⟨by
  simp [μ2]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩

theorem T1_allCompliers
    {Ω : Type*} [MeasurableSpace Ω]
    (P : PotentialOutcomes Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hind : P.Independence μ) (hexcl : P.Exclusion)
    (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0)
    (hCeq : P.compliers = Set.univ)
    (z : Bool) :
    P.waldEstimand μ = ∫ ω, P.outcome z true ω - P.outcome z false ω ∂μ := by
  have hmono : P.Monotonicity := by
    intro ω
    have hmem : P.type ω = .complier := by
      have h : ω ∈ P.compliers := by
        rw [hCeq]
        exact Set.mem_univ ω
      simpa [PotentialOutcomes.compliers] using h
    simp [PotentialOutcomes.type] at hmem
    cases h0 : P.treatment false ω <;> cases h1 : P.treatment true ω <;>
      simp_all [complianceType]
  have hC : μ P.compliers ≠ 0 := by
    rw [hCeq]
    simp
  rw [P.waldEstimand_eq_late hind hexcl hmono hY hZ hC z, hCeq, cond_univ]

/-- Defier model on `Bool × (Bool × Bool)` for T2. -/
noncomputable def defierWitness :
    PotentialOutcomes (Bool × (Bool × Bool)) where
  instrument := Prod.fst
  treatment := fun z ω => if ω.2.1 then z else if ω.2.2 then !z else false
  outcome := fun _ d ω =>
    if d then (if ω.2.1 then (1 : ℝ) else if ω.2.2 then 3 else 1) else 0
  measurable_instrument := measurable_fst
  measurable_treatment := fun _ => measurable_of_countable _
  measurable_outcome := fun _ _ => measurable_of_countable _

theorem defier_independence :
    defierWitness.Independence (μ2.prod (μ2.prod μ2)) :=
  indepFun_prod (X := id)
    (Y := fun b : Bool × Bool =>
      ((fun z => if b.1 then z else if b.2 then !z else false),
        fun (_ : Bool) (d : Bool) =>
          if d then (if b.1 then (1 : ℝ) else if b.2 then 3 else 1) else 0))
    measurable_id (measurable_of_countable _)

theorem defier_exclusion : defierWitness.Exclusion :=
  fun _ _ => rfl

theorem defier_arms_pos :
    ∀ z, (μ2.prod (μ2.prod μ2))
      (defierWitness.instrument ⁻¹' {z}) ≠ 0 := by
  intro z
  rw [show defierWitness.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by
    ext x; simp [defierWitness]]
  rw [Measure.prod_prod, measure_univ]
  simp [μ2_singleton]

theorem defier_not_monotone : ¬ defierWitness.Monotonicity := by
  intro hmono
  have h := hmono (false, (false, true))
  simp [defierWitness] at h
  exact absurd h (by decide)

theorem defier_compliers_eq :
    defierWitness.compliers = Set.univ ×ˢ ({true} ×ˢ Set.univ) := by
  ext ⟨z0, b1, b2⟩
  cases b1 <;> cases b2 <;>
    simp [PotentialOutcomes.compliers, PotentialOutcomes.type,
      complianceType, defierWitness]

theorem defier_complier_pos :
    (μ2.prod (μ2.prod μ2)) defierWitness.compliers ≠ 0 := by
  rw [defier_compliers_eq, Measure.prod_prod, Measure.prod_prod, measure_univ]
  simp [μ2_singleton]

theorem defier_effect_pos :
    ∀ ω z, 0 < defierWitness.outcome z true ω -
      defierWitness.outcome z false ω := by
  intro ω z
  cases h1 : ω.2.1 <;> cases h2 : ω.2.2 <;> simp [defierWitness, h1, h2]

theorem defier_arm_true :
    defierWitness.instrument ⁻¹' {true} = {true} ×ˢ Set.univ := by
  ext x; simp [defierWitness]

theorem defier_arm_false :
    defierWitness.instrument ⁻¹' {false} = {false} ×ˢ Set.univ := by
  ext x; simp [defierWitness]

theorem arm_true_mass :
    (μ2.prod (μ2.prod μ2)) ({true} ×ˢ (Set.univ : Set (Bool × Bool))) = 2⁻¹ := by
  rw [Measure.prod_prod, measure_univ, μ2_singleton, mul_one]

theorem arm_false_mass :
    (μ2.prod (μ2.prod μ2)) ({false} ×ˢ (Set.univ : Set (Bool × Bool))) = 2⁻¹ := by
  rw [Measure.prod_prod, measure_univ, μ2_singleton, mul_one]

theorem singleton_mass (z0 b1 b2 : Bool) :
    (μ2.prod (μ2.prod μ2)) ({(z0, (b1, b2))} : Set (Bool × (Bool × Bool))) =
      2⁻¹ * (2⁻¹ * 2⁻¹) := by
  have h1 : ({(z0, (b1, b2))} : Set (Bool × (Bool × Bool))) =
      {z0} ×ˢ ({(b1, b2)} : Set (Bool × Bool)) := by
    ext x; simp
  have h2 : ({(b1, b2)} : Set (Bool × Bool)) = {b1} ×ˢ {b2} := by
    ext x; simp
  rw [h1, Measure.prod_prod, h2, Measure.prod_prod, μ2_singleton, μ2_singleton,
    μ2_singleton]

theorem cond_true_true (b1 b2 : Bool) :
    ((μ2.prod (μ2.prod μ2))[|{true} ×ˢ (Set.univ : Set (Bool × Bool))]).real
      ({(true, (b1, b2))} : Set (Bool × (Bool × Bool))) = 1/4 := by
  rw [measureReal_def]
  have hmeas : MeasurableSet ({true} ×ˢ (Set.univ : Set (Bool × Bool))) :=
    MeasurableSet.prod (measurableSet_singleton true) MeasurableSet.univ
  rw [cond_apply hmeas]
  have hinter : ({true} ×ˢ (Set.univ : Set (Bool × Bool))) ∩
      ({(true, (b1, b2))} : Set (Bool × (Bool × Bool))) =
      ({(true, (b1, b2))} : Set (Bool × (Bool × Bool))) := by
    ext x; simp
  rw [hinter, singleton_mass, arm_true_mass]
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

theorem cond_true_false (b1 b2 : Bool) :
    ((μ2.prod (μ2.prod μ2))[|{true} ×ˢ (Set.univ : Set (Bool × Bool))]).real
      ({(false, (b1, b2))} : Set (Bool × (Bool × Bool))) = 0 := by
  rw [measureReal_def]
  have hmeas : MeasurableSet ({true} ×ˢ (Set.univ : Set (Bool × Bool))) :=
    MeasurableSet.prod (measurableSet_singleton true) MeasurableSet.univ
  rw [cond_apply hmeas]
  have hinter : ({true} ×ˢ (Set.univ : Set (Bool × Bool))) ∩
      ({(false, (b1, b2))} : Set (Bool × (Bool × Bool))) = ∅ := by
    ext x; simp
  rw [hinter, measure_empty, mul_zero, ENNReal.toReal_zero]

theorem cond_false_true (b1 b2 : Bool) :
    ((μ2.prod (μ2.prod μ2))[|{false} ×ˢ (Set.univ : Set (Bool × Bool))]).real
      ({(true, (b1, b2))} : Set (Bool × (Bool × Bool))) = 0 := by
  rw [measureReal_def]
  have hmeas : MeasurableSet ({false} ×ˢ (Set.univ : Set (Bool × Bool))) :=
    MeasurableSet.prod (measurableSet_singleton false) MeasurableSet.univ
  rw [cond_apply hmeas]
  have hinter : ({false} ×ˢ (Set.univ : Set (Bool × Bool))) ∩
      ({(true, (b1, b2))} : Set (Bool × (Bool × Bool))) = ∅ := by
    ext x; simp
  rw [hinter, measure_empty, mul_zero, ENNReal.toReal_zero]

theorem cond_false_false (b1 b2 : Bool) :
    ((μ2.prod (μ2.prod μ2))[|{false} ×ˢ (Set.univ : Set (Bool × Bool))]).real
      ({(false, (b1, b2))} : Set (Bool × (Bool × Bool))) = 1/4 := by
  rw [measureReal_def]
  have hmeas : MeasurableSet ({false} ×ˢ (Set.univ : Set (Bool × Bool))) :=
    MeasurableSet.prod (measurableSet_singleton false) MeasurableSet.univ
  rw [cond_apply hmeas]
  have hinter : ({false} ×ˢ (Set.univ : Set (Bool × Bool))) ∩
      ({(false, (b1, b2))} : Set (Bool × (Bool × Bool))) =
      ({(false, (b1, b2))} : Set (Bool × (Bool × Bool))) := by
    ext x; simp
  rw [hinter, singleton_mass, arm_false_mass]
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

theorem treated_TTT : defierWitness.treated (true, (true, true)) = 1 := by
  simp [PotentialOutcomes.treated, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem treated_TTF : defierWitness.treated (true, (true, false)) = 1 := by
  simp [PotentialOutcomes.treated, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem treated_TFT : defierWitness.treated (true, (false, true)) = 0 := by
  simp [PotentialOutcomes.treated, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem treated_TFF : defierWitness.treated (true, (false, false)) = 0 := by
  simp [PotentialOutcomes.treated, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem treated_FTT : defierWitness.treated (false, (true, true)) = 0 := by
  simp [PotentialOutcomes.treated, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem treated_FTF : defierWitness.treated (false, (true, false)) = 0 := by
  simp [PotentialOutcomes.treated, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem treated_FFT : defierWitness.treated (false, (false, true)) = 1 := by
  simp [PotentialOutcomes.treated, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem treated_FFF : defierWitness.treated (false, (false, false)) = 0 := by
  simp [PotentialOutcomes.treated, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem outcome_TTT : defierWitness.observedOutcome (true, (true, true)) = 1 := by
  simp [PotentialOutcomes.observedOutcome, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem outcome_TTF : defierWitness.observedOutcome (true, (true, false)) = 1 := by
  simp [PotentialOutcomes.observedOutcome, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem outcome_TFT : defierWitness.observedOutcome (true, (false, true)) = 0 := by
  simp [PotentialOutcomes.observedOutcome, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem outcome_TFF :
    defierWitness.observedOutcome (true, (false, false)) = 0 := by
  simp [PotentialOutcomes.observedOutcome, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem outcome_FTT : defierWitness.observedOutcome (false, (true, true)) = 0 := by
  simp [PotentialOutcomes.observedOutcome, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem outcome_FTF : defierWitness.observedOutcome (false, (true, false)) = 0 := by
  simp [PotentialOutcomes.observedOutcome, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem outcome_FFT : defierWitness.observedOutcome (false, (false, true)) = 3 := by
  simp [PotentialOutcomes.observedOutcome, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem outcome_FFF :
    defierWitness.observedOutcome (false, (false, false)) = 0 := by
  simp [PotentialOutcomes.observedOutcome, PotentialOutcomes.observedTreatment,
    defierWitness]

theorem defier_treated_true :
    defierWitness.armMean (μ2.prod (μ2.prod μ2))
      defierWitness.treated true = 1/2 := by
  unfold PotentialOutcomes.armMean
  rw [defier_arm_true]
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cond_true_true,
    cond_true_false, treated_TTT, treated_TTF, treated_TFT, treated_TFF]
  norm_num

theorem defier_treated_false :
    defierWitness.armMean (μ2.prod (μ2.prod μ2))
      defierWitness.treated false = 1/4 := by
  unfold PotentialOutcomes.armMean
  rw [defier_arm_false]
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cond_false_true,
    cond_false_false, treated_FTT, treated_FTF, treated_FFT, treated_FFF]
  norm_num

theorem defier_outcome_true :
    defierWitness.armMean (μ2.prod (μ2.prod μ2))
      defierWitness.observedOutcome true = 1/2 := by
  unfold PotentialOutcomes.armMean
  rw [defier_arm_true]
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cond_true_true,
    cond_true_false, outcome_TTT, outcome_TTF, outcome_TFT, outcome_TFF]
  norm_num

theorem defier_outcome_false :
    defierWitness.armMean (μ2.prod (μ2.prod μ2))
      defierWitness.observedOutcome false = 3/4 := by
  unfold PotentialOutcomes.armMean
  rw [defier_arm_false]
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cond_false_true,
    cond_false_false, outcome_FTT, outcome_FTF, outcome_FFT, outcome_FFF]
  norm_num

theorem compliers_mass :
    (μ2.prod (μ2.prod μ2))
      ((Set.univ : Set Bool) ×ˢ (({true} : Set Bool) ×ˢ (Set.univ : Set Bool))) =
      2⁻¹ := by
  rw [Measure.prod_prod, Measure.prod_prod, measure_univ, μ2_singleton]
  simp

theorem cond_compl_T (z0 b2 : Bool) :
    ((μ2.prod (μ2.prod μ2))[|(Set.univ : Set Bool) ×ˢ
      (({true} : Set Bool) ×ˢ (Set.univ : Set Bool))]).real
      ({(z0, (true, b2))} : Set (Bool × (Bool × Bool))) = 1/4 := by
  rw [measureReal_def]
  have hmeas : MeasurableSet ((Set.univ : Set Bool) ×ˢ
      (({true} : Set Bool) ×ˢ (Set.univ : Set Bool))) :=
    MeasurableSet.prod MeasurableSet.univ
      (MeasurableSet.prod (measurableSet_singleton true) MeasurableSet.univ)
  rw [cond_apply hmeas]
  have hinter : ((Set.univ : Set Bool) ×ˢ
      (({true} : Set Bool) ×ˢ (Set.univ : Set Bool))) ∩
      ({(z0, (true, b2))} : Set (Bool × (Bool × Bool))) =
      ({(z0, (true, b2))} : Set (Bool × (Bool × Bool))) := by
    ext x; simp
  rw [hinter, singleton_mass, compliers_mass]
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

theorem cond_compl_F (z0 b2 : Bool) :
    ((μ2.prod (μ2.prod μ2))[|(Set.univ : Set Bool) ×ˢ
      (({true} : Set Bool) ×ˢ (Set.univ : Set Bool))]).real
      ({(z0, (false, b2))} : Set (Bool × (Bool × Bool))) = 0 := by
  rw [measureReal_def]
  have hmeas : MeasurableSet ((Set.univ : Set Bool) ×ˢ
      (({true} : Set Bool) ×ˢ (Set.univ : Set Bool))) :=
    MeasurableSet.prod MeasurableSet.univ
      (MeasurableSet.prod (measurableSet_singleton true) MeasurableSet.univ)
  rw [cond_apply hmeas]
  have hinter : ((Set.univ : Set Bool) ×ˢ
      (({true} : Set Bool) ×ˢ (Set.univ : Set Bool))) ∩
      ({(z0, (false, b2))} : Set (Bool × (Bool × Bool))) = ∅ := by
    ext x; simp
  rw [hinter, measure_empty, mul_zero, ENNReal.toReal_zero]

theorem outcomeDiff_TTT (z : Bool) :
    defierWitness.outcome z true (true, (true, true)) -
      defierWitness.outcome z false (true, (true, true)) = 1 := by
  simp [defierWitness]

theorem outcomeDiff_TTF (z : Bool) :
    defierWitness.outcome z true (true, (true, false)) -
      defierWitness.outcome z false (true, (true, false)) = 1 := by
  simp [defierWitness]

theorem outcomeDiff_FTT (z : Bool) :
    defierWitness.outcome z true (false, (true, true)) -
      defierWitness.outcome z false (false, (true, true)) = 1 := by
  simp [defierWitness]

theorem outcomeDiff_FTF (z : Bool) :
    defierWitness.outcome z true (false, (true, false)) -
      defierWitness.outcome z false (false, (true, false)) = 1 := by
  simp [defierWitness]

theorem defier_complierAvg (z : Bool) :
    (∫ ω, defierWitness.outcome z true ω -
      defierWitness.outcome z false ω
      ∂(μ2.prod (μ2.prod μ2))[|defierWitness.compliers]) = 1 := by
  rw [defier_compliers_eq]
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cond_compl_T,
    cond_compl_F, outcomeDiff_TTT, outcomeDiff_TTF, outcomeDiff_FTT,
    outcomeDiff_FTF]
  norm_num

theorem defier_firstStage :
    defierWitness.armMean (μ2.prod (μ2.prod μ2)) defierWitness.treated true -
      defierWitness.armMean (μ2.prod (μ2.prod μ2)) defierWitness.treated false =
      1/4 := by
  rw [defier_treated_true, defier_treated_false]
  norm_num

theorem defier_wald :
    defierWitness.waldEstimand (μ2.prod (μ2.prod μ2)) = -1 := by
  unfold PotentialOutcomes.waldEstimand
  rw [defier_outcome_true, defier_outcome_false, defier_treated_true,
    defier_treated_false]
  norm_num

theorem defier_wald_ne (z : Bool) :
    defierWitness.waldEstimand (μ2.prod (μ2.prod μ2)) ≠
      ∫ ω, defierWitness.outcome z true ω -
        defierWitness.outcome z false ω
        ∂(μ2.prod (μ2.prod μ2))[|defierWitness.compliers] := by
  rw [defier_wald, defier_complierAvg]
  norm_num

/-- Model A on `Bool × Bool` for T3. -/
noncomputable def obsWitnessA : PotentialOutcomes (Bool × Bool) where
  instrument := Prod.fst
  treatment := fun z ω => z && ω.2
  outcome := fun _ d _ => if d then (1 : ℝ) else 0
  measurable_instrument := measurable_fst
  measurable_treatment := fun _ => measurable_of_countable _
  measurable_outcome := fun _ _ => measurable_const

/-- Model B on `Bool × Bool` for T3. -/
noncomputable def obsWitnessB : PotentialOutcomes (Bool × Bool) where
  instrument := Prod.fst
  treatment := fun z ω => z && ω.2
  outcome := fun _ d ω => if d then (if ω.2 then (1 : ℝ) else 5) else 0
  measurable_instrument := measurable_fst
  measurable_treatment := fun _ => measurable_of_countable _
  measurable_outcome := fun _ _ => measurable_of_countable _

theorem obs_triple_eq :
    (fun ω : Bool × Bool =>
      (obsWitnessA.instrument ω, obsWitnessA.observedTreatment ω,
        obsWitnessA.observedOutcome ω)) =
    (fun ω : Bool × Bool =>
      (obsWitnessB.instrument ω, obsWitnessB.observedTreatment ω,
        obsWitnessB.observedOutcome ω)) := by
  funext ⟨z0, b⟩
  cases z0 <;> cases b <;>
    simp [PotentialOutcomes.observedTreatment, PotentialOutcomes.observedOutcome,
      obsWitnessA, obsWitnessB]

theorem obs_map_eq :
    Measure.map (fun ω : Bool × Bool =>
        (obsWitnessA.instrument ω, obsWitnessA.observedTreatment ω,
          obsWitnessA.observedOutcome ω)) (μ2.prod μ2) =
      Measure.map (fun ω : Bool × Bool =>
        (obsWitnessB.instrument ω, obsWitnessB.observedTreatment ω,
          obsWitnessB.observedOutcome ω)) (μ2.prod μ2) := by
  rw [obs_triple_eq]

theorem obsA_independence : obsWitnessA.Independence (μ2.prod μ2) :=
  indepFun_prod (X := id)
    (Y := fun b : Bool => ((fun z => z && b),
      fun (_ : Bool) (d : Bool) => if d then (1 : ℝ) else 0))
    measurable_id (measurable_of_countable _)

theorem obsB_independence : obsWitnessB.Independence (μ2.prod μ2) :=
  indepFun_prod (X := id)
    (Y := fun b : Bool => ((fun z => z && b),
      fun (_ : Bool) (d : Bool) => if d then (if b then (1 : ℝ) else 5) else 0))
    measurable_id (measurable_of_countable _)

theorem obsA_exclusion : obsWitnessA.Exclusion := fun _ _ => rfl

theorem obsB_exclusion : obsWitnessB.Exclusion := fun _ _ => rfl

theorem obsA_monotone : obsWitnessA.Monotonicity := by
  intro ω
  cases h : ω.2 <;> simp [obsWitnessA, h]

theorem obsB_monotone : obsWitnessB.Monotonicity := by
  intro ω
  cases h : ω.2 <;> simp [obsWitnessB, h]

theorem obsA_arms :
    ∀ z, (μ2.prod μ2) (obsWitnessA.instrument ⁻¹' {z}) ≠ 0 := by
  intro z
  rw [show obsWitnessA.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by
    ext x; simp [obsWitnessA]]
  rw [Measure.prod_prod, measure_univ]
  simp [μ2_singleton]

theorem obsB_arms :
    ∀ z, (μ2.prod μ2) (obsWitnessB.instrument ⁻¹' {z}) ≠ 0 := by
  intro z
  rw [show obsWitnessB.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by
    ext x; simp [obsWitnessB]]
  rw [Measure.prod_prod, measure_univ]
  simp [μ2_singleton]

theorem obsA_compliers : obsWitnessA.compliers = Set.univ ×ˢ {true} := by
  ext ⟨a, b⟩
  cases b <;> simp [PotentialOutcomes.compliers, PotentialOutcomes.type,
    complianceType, obsWitnessA]

theorem obsB_compliers : obsWitnessB.compliers = Set.univ ×ˢ {true} := by
  ext ⟨a, b⟩
  cases b <;> simp [PotentialOutcomes.compliers, PotentialOutcomes.type,
    complianceType, obsWitnessB]

theorem obsA_complier_pos : (μ2.prod μ2) obsWitnessA.compliers ≠ 0 := by
  rw [obsA_compliers, Measure.prod_prod, measure_univ]
  simp [μ2_singleton]

theorem obsB_complier_pos : (μ2.prod μ2) obsWitnessB.compliers ≠ 0 := by
  rw [obsB_compliers, Measure.prod_prod, measure_univ]
  simp [μ2_singleton]

theorem obs_wald_eq :
    obsWitnessA.waldEstimand (μ2.prod μ2) =
      obsWitnessB.waldEstimand (μ2.prod μ2) :=
  waldEstimand_eq_of_map_eq _ _ _ _ obs_map_eq

theorem obsA_complierAvg (z : Bool) :
    (∫ ω, obsWitnessA.outcome z true ω - obsWitnessA.outcome z false ω
      ∂(μ2.prod μ2)[|obsWitnessA.compliers]) = 1 := by
  have hC : (μ2.prod μ2) obsWitnessA.compliers ≠ 0 := obsA_complier_pos
  have := cond_isProbabilityMeasure (μ := μ2.prod μ2) hC
  rw [show (fun ω : Bool × Bool => obsWitnessA.outcome z true ω -
      obsWitnessA.outcome z false ω) = fun _ => 1 by
    funext ω; simp [obsWitnessA]]
  simp

theorem obs_complier_eq (z z' : Bool) :
    (∫ ω, obsWitnessA.outcome z true ω - obsWitnessA.outcome z false ω
      ∂(μ2.prod μ2)[|obsWitnessA.compliers]) =
    (∫ ω, obsWitnessB.outcome z' true ω - obsWitnessB.outcome z' false ω
      ∂(μ2.prod μ2)[|obsWitnessB.compliers]) :=
  late_eq_of_map_eq _ _ _ _ obsA_independence obsA_exclusion obsA_monotone
    (fun _ _ => Integrable.of_finite) obsA_arms obsA_complier_pos
    obsB_independence obsB_exclusion obsB_monotone
    (fun _ _ => Integrable.of_finite) obsB_arms obsB_complier_pos
    obs_map_eq z z'

theorem obsB_complierAvg (z' : Bool) :
    (∫ ω, obsWitnessB.outcome z' true ω - obsWitnessB.outcome z' false ω
      ∂(μ2.prod μ2)[|obsWitnessB.compliers]) = 1 := by
  rw [← obs_complier_eq true z', obsA_complierAvg]

theorem pop_avg_A (z : Bool) :
    (∫ ω, obsWitnessA.outcome z true ω - obsWitnessA.outcome z false ω
      ∂(μ2.prod μ2)) = 1 := by
  rw [show (fun ω : Bool × Bool => obsWitnessA.outcome z true ω -
      obsWitnessA.outcome z false ω) = fun _ => 1 by
    funext ω; simp [obsWitnessA]]
  simp

theorem singleton_2 (a b : Bool) :
    (μ2.prod μ2) ({(a, b)} : Set (Bool × Bool)) = 2⁻¹ * 2⁻¹ := by
  have h : ({(a, b)} : Set (Bool × Bool)) = {a} ×ˢ {b} := by
    ext x; simp
  rw [h, Measure.prod_prod, μ2_singleton, μ2_singleton]

theorem real_singleton_2 (a b : Bool) :
    (μ2.prod μ2).real ({(a, b)} : Set (Bool × Bool)) = 1/4 := by
  rw [measureReal_def, singleton_2]
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

theorem diff_TT (z : Bool) :
    obsWitnessB.outcome z true (true, true) -
      obsWitnessB.outcome z false (true, true) = 1 := by
  simp [obsWitnessB]

theorem diff_TF (z : Bool) :
    obsWitnessB.outcome z true (true, false) -
      obsWitnessB.outcome z false (true, false) = 5 := by
  simp [obsWitnessB]

theorem diff_FT (z : Bool) :
    obsWitnessB.outcome z true (false, true) -
      obsWitnessB.outcome z false (false, true) = 1 := by
  simp [obsWitnessB]

theorem diff_FF (z : Bool) :
    obsWitnessB.outcome z true (false, false) -
      obsWitnessB.outcome z false (false, false) = 5 := by
  simp [obsWitnessB]

theorem pop_avg_B (z : Bool) :
    (∫ ω, obsWitnessB.outcome z true ω - obsWitnessB.outcome z false ω
      ∂(μ2.prod μ2)) = 3 := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, real_singleton_2,
    diff_TT, diff_TF, diff_FT, diff_FF]
  norm_num

theorem population_not_identified :
    ¬ ∃ g : Measure (Bool × Bool × ℝ) → ℝ,
      g (Measure.map (fun ω : Bool × Bool =>
        (obsWitnessA.instrument ω, obsWitnessA.observedTreatment ω,
          obsWitnessA.observedOutcome ω)) (μ2.prod μ2)) =
        ∫ ω, obsWitnessA.outcome true true ω -
          obsWitnessA.outcome true false ω ∂(μ2.prod μ2) ∧
      g (Measure.map (fun ω : Bool × Bool =>
        (obsWitnessB.instrument ω, obsWitnessB.observedTreatment ω,
          obsWitnessB.observedOutcome ω)) (μ2.prod μ2)) =
        ∫ ω, obsWitnessB.outcome true true ω -
          obsWitnessB.outcome true false ω ∂(μ2.prod μ2) := by
  rintro ⟨g, hA, hB⟩
  rw [pop_avg_A true] at hA
  rw [pop_avg_B true] at hB
  rw [obs_map_eq] at hA
  rw [hA] at hB
  norm_num at hB

end MathlibExtTest.Probability.Causality.InstrumentalVariable

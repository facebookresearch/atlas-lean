/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Consistency
public import MathlibExtTest.Probability.Statistics.Survival.Censoring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Statistics.Censoring
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.SurvivalConsistency

namespace MathlibExtTest.Probability.Statistics.SurvivalConsistency

/-! ### `empiricalData` counts subjects -/

/-- Three subjects, all with `(T, C) = (1, 1)`: all three are at risk at `j = 1` and all three are
observed to die there (a tie counts as an event). -/
example :
    (empiricalData (fun _ (_ : Unit) => ((1 : Fin 2), (1 : Fin 2))) 3 ()).atRisk 1 = 3 ∧
      (empiricalData (fun _ (_ : Unit) => ((1 : Fin 2), (1 : Fin 2))) 3 ()).deaths 1 = 3 := by
  decide

/-- One subject with `(T, C) = (1, 0)` is censored at `j = 0`, so no death is recorded. -/
example : (empiricalData (fun _ (_ : Unit) => ((1 : Fin 2), (0 : Fin 2))) 1 ()).deaths 0 = 0 := by
  decide

example : gridTime (2 : Fin 3) = 2 := by norm_num [gridTime]

/-! ### Deliverable 1 at an explicit cell -/

/-- With the `Fin 3` laws of the Censoring tests (`P(X ≥ 1) = 3/8`), on the canonical sequence
space the at-risk proportion at `j = 1` converges almost surely to `3/8`. -/
example :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ =>
        indepLaw MathlibExtTest.Probability.Statistics.Censoring.pT
          MathlibExtTest.Probability.Statistics.Censoring.pC),
      Tendsto (fun n : ℕ => ((empiricalData (fun i ω => ω i) n ω).atRisk 1 : ℝ) / n) atTop
        (𝓝 (3 / 8)) := by
  rw [← MathlibExtTest.Probability.Statistics.Censoring.obsAtRiskMass_indepLaw_values.2.1]
  exact ae_tendsto_atRisk_div
    (ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (measurePreserving_eval_infinitePi _ i).hasLaw) 1

/-- The death proportion at `j = 2` converges almost surely to `P(X = 2, δ = 1) = 1/8`. -/
example :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ =>
        indepLaw MathlibExtTest.Probability.Statistics.Censoring.pT
          MathlibExtTest.Probability.Statistics.Censoring.pC),
      Tendsto (fun n : ℕ => ((empiricalData (fun i ω => ω i) n ω).deaths 2 : ℝ) / n) atTop
        (𝓝 (1 / 8)) := by
  rw [← MathlibExtTest.Probability.Statistics.Censoring.obsEventMass_indepLaw_values.2.2]
  exact ae_tendsto_deaths_div
    (ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (measurePreserving_eval_infinitePi _ i).hasLaw) 2

/-! ### Deliverable 2 on the trivial grid `k = 1` -/

/-- On a one-point grid the at-risk mass at `0` is `1`. -/
theorem obsAtRiskMass_fin_one (pT pC : PMF (Fin 1)) : obsAtRiskMass (indepLaw pT pC) 0 = 1 := by
  have hs : {ω : Fin 1 × Fin 1 | (0 : Fin 1) ≤ min ω.1 ω.2} = Set.univ :=
    Set.eq_univ_of_forall fun ω => Fin.zero_le _
  rw [obsAtRiskMass, hs, probReal_univ]

/-- On a one-point grid every subject fails at `0`, so the Kaplan–Meier estimate at `0`
converges to `P(T > 0) = 0`. -/
example (pT pC : PMF (Fin 1)) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => indepLaw pT pC),
      Tendsto (fun n : ℕ => (empiricalData (fun i ω => ω i) n ω).kmSurvival ((0 : ℕ) : ℝ))
        atTop (𝓝 0) := by
  have h := ae_tendsto_kmSurvival_infinitePi pT pC 0 (by simp [obsAtRiskMass_fin_one])
  have hs : {t : Fin 1 | (0 : Fin 1) < t} = ∅ := by
    ext t; simp [Fin.lt_def]
  rwa [hs, measureReal_empty] at h

/-! ### Deliverable 2 with computed hazards on `Fin 2` -/

/-- Event-time law `P(T = 0, 1) = 1/4, 3/4`. -/
noncomputable def pT2 : PMF (Fin 2) :=
  PMF.ofFintype (fun i => ((![1 / 4, 3 / 4] : Fin 2 → ℝ≥0) i : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fin.sum_univ_two]
    norm_num)

/-- Censoring-time law `P(C = 0, 1) = 1/2, 1/2`. -/
noncomputable def pC2 : PMF (Fin 2) :=
  PMF.ofFintype (fun i => ((![1 / 2, 1 / 2] : Fin 2 → ℝ≥0) i : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fin.sum_univ_two]
    norm_num)

theorem survivalMass_pT2 : survivalMass pT2 0 = 1 ∧ survivalMass pT2 1 = 3 / 4 := by
  simp only [survivalMass_eq_sum]
  constructor
  · simp [Fin.sum_univ_two, pT2]; norm_num
  · simp [Finset.sum_filter, Fin.sum_univ_two, pT2]

theorem survivalMass_pC2 : survivalMass pC2 0 = 1 ∧ survivalMass pC2 1 = 1 / 2 := by
  simp only [survivalMass_eq_sum]
  constructor
  · simp [Fin.sum_univ_two, pC2]; norm_num
  · simp [Finset.sum_filter, Fin.sum_univ_two, pC2]

/-- The hazard of `T`: `h(0) = 1/4`, `h(1) = 1`. -/
theorem hazard_pT2 : hazard pT2 0 = 1 / 4 ∧ hazard pT2 1 = 1 := by
  obtain ⟨s0, s1⟩ := survivalMass_pT2
  simp only [hazard, s0, s1]
  refine ⟨?_, ?_⟩ <;> simp [pT2]

/-- `P(X ≥ 1) = 3/4 · 1/2 = 3/8 ≠ 0`. -/
theorem obsAtRiskMass_pT2_pC2 : obsAtRiskMass (indepLaw pT2 pC2) 1 = 3 / 8 := by
  rw [obsAtRiskMass_indepLaw, survivalMass_pT2.2, survivalMass_pC2.2]
  norm_num

/-- The Kaplan–Meier estimate at time `0` converges almost surely to `1 - h(0) = 3/4`. -/
example :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => indepLaw pT2 pC2),
      Tendsto (fun n : ℕ => (empiricalData (fun i ω => ω i) n ω).kmSurvival ((0 : ℕ) : ℝ))
        atTop (𝓝 (3 / 4)) := by
  have hm : obsAtRiskMass (indepLaw pT2 pC2) 0 ≠ 0 := by
    rw [obsAtRiskMass_indepLaw, survivalMass_pT2.1, survivalMass_pC2.1]; norm_num
  have h := ae_tendsto_kmSurvival (P := Measure.infinitePi fun _ : ℕ => indepLaw pT2 pC2)
    pT2 pC2 (ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (measurePreserving_eval_infinitePi (fun _ : ℕ => indepLaw pT2 pC2) i).hasLaw) 0 hm
  have hfilter : ({j | j ≤ (0 : Fin 2)} : Finset (Fin 2)) = {0} := by decide
  rw [hfilter, prod_singleton, hazard_pT2.1] at h
  rwa [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at h

/-- At the top grid index `m = 1` the limit `(1 - 1/4)(1 - 1) = 0` is `P(T > 1) = 0`. -/
example : ∏ j with j ≤ (1 : Fin 2), (1 - hazard pT2 j) = 0 ∧
    pT2.toMeasure.real {t | (1 : Fin 2) < t} = 0 := by
  have h := prod_one_sub_hazard pT2 1 (by rw [survivalMass_pT2.2]; norm_num)
  have hs : {t : Fin 2 | (1 : Fin 2) < t} = ∅ := by
    ext t; fin_cases t <;> simp
  rw [hs, measureReal_empty] at h
  exact ⟨h, by rw [hs, measureReal_empty]⟩

/-- The hypothesis of `ae_tendsto_kmSurvival` at the top index holds for this model. -/
example : obsAtRiskMass (indepLaw pT2 pC2) 1 ≠ 0 := by
  rw [obsAtRiskMass_pT2_pC2]; norm_num

/-- The prefix product before the top index is the survival mass: `1 - h(0) = 3/4 = P(T ≥ 1)`. -/
example : ∏ l with l < (1 : Fin 2), (1 - hazard pT2 l) = 3 / 4 := by
  rw [prod_lt_one_sub_hazard pT2 1 (by rw [survivalMass_pT2.2]; norm_num), survivalMass_pT2.2]

/-! ### Deliverable 3: competing risks -/

open MathlibExt.Probability.Statistics.CompetingRisks

/-- Two subjects: `((T, J), C) = ((1, 0), 1)` fails from cause `0` at `1` (a tie is an event), and
`((1, 1), 0)` is censored at `0`. -/
example :
    (empiricalCauseData (fun i (_ : Unit) =>
        if i = 0 then (((1 : Fin 2), (0 : Fin 2)), (1 : Fin 2))
        else (((1 : Fin 2), (1 : Fin 2)), (0 : Fin 2))) 2 ()).events 1 0 = 1 ∧
    (empiricalCauseData (fun i (_ : Unit) =>
        if i = 0 then (((1 : Fin 2), (0 : Fin 2)), (1 : Fin 2))
        else (((1 : Fin 2), (1 : Fin 2)), (0 : Fin 2))) 2 ()).censored 0 = 1 := by
  decide

/-- On a one-point grid with one cause, the at-risk mass at `0` is `1`. -/
theorem causeAtRiskMass_fin_one (pTJ : PMF (Fin 1 × Fin 1)) (pC : PMF (Fin 1)) :
    causeAtRiskMass (indepCauseLaw pTJ pC) 0 = 1 := by
  have hs : {ω : (Fin 1 × Fin 1) × Fin 1 | (0 : Fin 1) ≤ min ω.1.1 ω.2} = Set.univ :=
    Set.eq_univ_of_forall fun ω => Fin.zero_le _
  have : IsProbabilityMeasure (indepCauseLaw pTJ pC) := by
    unfold indepCauseLaw; infer_instance
  rw [causeAtRiskMass, hs, probReal_univ]

/-- On a one-point grid with one cause, every subject fails from cause `0` at time `0`, so on the
canonical sequence space the estimated cumulative incidence at `0` converges to `1`. -/
example (pTJ : PMF (Fin 1 × Fin 1)) (pC : PMF (Fin 1)) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => indepCauseLaw pTJ pC),
      Tendsto (fun n : ℕ =>
        (empiricalCauseData (fun i ω => ω i) n ω).cumulativeIncidence 0 ((0 : ℕ) : ℝ))
        atTop (𝓝 1) := by
  have : IsProbabilityMeasure (indepCauseLaw pTJ pC) := by
    unfold indepCauseLaw; infer_instance
  have h := ae_tendsto_cumulativeIncidence pTJ pC
    (ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (measurePreserving_eval_infinitePi (fun _ : ℕ => indepCauseLaw pTJ pC) i).hasLaw)
    0 (by simp [causeAtRiskMass_fin_one]) 0
  have hs : {x : Fin 1 × Fin 1 | x.1 ≤ 0 ∧ x.2 = 0} = Set.univ :=
    Set.eq_univ_of_forall fun x => ⟨le_of_eq (Subsingleton.elim (α := Fin 1) _ _),
      Subsingleton.elim (α := Fin 1) _ _⟩
  rwa [hs, probReal_univ] at h

/-- Forgetting causes of `empiricalCauseData` gives `empiricalData` of `(T, C)`. -/
example (W : ℕ → Unit → (Fin 2 × Fin 3) × Fin 2) (n : ℕ) :
    (empiricalCauseData W n ()).toCensoredData.atRisk 1 =
      (empiricalData (fun i ω => ((W i ω).1.1, (W i ω).2)) n ()).atRisk 1 := by
  rw [toCensoredData_empiricalCauseData]

end MathlibExtTest.Probability.Statistics.SurvivalConsistency

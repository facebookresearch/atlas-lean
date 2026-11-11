/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Censoring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal NNReal
open MathlibExt.Probability.Statistics.Censoring

namespace MathlibExtTest.Probability.Statistics.Censoring

/-! ### An independent model on `Fin 3` -/

/-- Event-time law `P(T = 0, 1, 2) = 1/4, 1/4, 1/2`. -/
noncomputable def pT : PMF (Fin 3) :=
  PMF.ofFintype (fun i => ((![1 / 4, 1 / 4, 1 / 2] : Fin 3 → ℝ≥0) i : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fin.sum_univ_three]
    norm_num)

/-- Censoring-time law `P(C = 0, 1, 2) = 1/2, 1/4, 1/4`. -/
noncomputable def pC : PMF (Fin 3) :=
  PMF.ofFintype (fun i => ((![1 / 2, 1 / 4, 1 / 4] : Fin 3 → ℝ≥0) i : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fin.sum_univ_three]
    norm_num)

theorem pT_apply : (pT 0).toReal = 1 / 4 ∧ (pT 1).toReal = 1 / 4 ∧ (pT 2).toReal = 1 / 2 := by
  simp [pT]

theorem pC_apply : (pC 0).toReal = 1 / 2 ∧ (pC 1).toReal = 1 / 4 ∧ (pC 2).toReal = 1 / 4 := by
  simp [pC]

/-- `P(T ≥ j) = 1, 3/4, 1/2`, computed from the point masses. -/
theorem survivalMass_pT :
    survivalMass pT 0 = 1 ∧ survivalMass pT 1 = 3 / 4 ∧ survivalMass pT 2 = 1 / 2 := by
  simp only [survivalMass_eq_sum]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Finset.sum_filter, Fin.sum_univ_three, pT] <;> norm_num


/-- `P(C ≥ j) = 1, 1/2, 1/4`, computed from the point masses. -/
theorem survivalMass_pC :
    survivalMass pC 0 = 1 ∧ survivalMass pC 1 = 1 / 2 ∧ survivalMass pC 2 = 1 / 4 := by
  simp only [survivalMass_eq_sum]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Finset.sum_filter, Fin.sum_univ_three, pC] <;> norm_num

/-- The hazard of `T`: `1/4, 1/3, 1`. -/
theorem hazard_pT : hazard pT 0 = 1 / 4 ∧ hazard pT 1 = 1 / 3 ∧ hazard pT 2 = 1 := by
  obtain ⟨h0, h1, h2⟩ := pT_apply
  obtain ⟨s0, s1, s2⟩ := survivalMass_pT
  simp only [hazard, h0, h1, h2, s0, s1, s2]
  norm_num

/-- The event masses `P(X = j, δ = 1) = 1/4, 1/8, 1/8` via the factorization. -/
theorem obsEventMass_indepLaw_values :
    obsEventMass (indepLaw pT pC) 0 = 1 / 4 ∧ obsEventMass (indepLaw pT pC) 1 = 1 / 8 ∧
      obsEventMass (indepLaw pT pC) 2 = 1 / 8 := by
  obtain ⟨h0, h1, h2⟩ := pT_apply
  obtain ⟨s0, s1, s2⟩ := survivalMass_pC
  simp only [obsEventMass_indepLaw, h0, h1, h2, s0, s1, s2]
  norm_num

/-- The at-risk masses `P(X ≥ j) = 1, 3/8, 1/8` via the factorization. -/
theorem obsAtRiskMass_indepLaw_values :
    obsAtRiskMass (indepLaw pT pC) 0 = 1 ∧ obsAtRiskMass (indepLaw pT pC) 1 = 3 / 8 ∧
      obsAtRiskMass (indepLaw pT pC) 2 = 1 / 8 := by
  obtain ⟨t0, t1, t2⟩ := survivalMass_pT
  obtain ⟨s0, s1, s2⟩ := survivalMass_pC
  simp only [obsAtRiskMass_indepLaw, t0, t1, t2, s0, s1, s2]
  norm_num

/-- The identification theorem at every grid point: the observed ratio is the hazard of `T`. -/
theorem ratio_eq_hazard (j : Fin 3) :
    obsEventMass (indepLaw pT pC) j / obsAtRiskMass (indepLaw pT pC) j = hazard pT j := by
  obtain ⟨s0, s1, s2⟩ := survivalMass_pC
  refine obsEventMass_div_obsAtRiskMass pT pC j ?_
  fin_cases j <;> simp [s0, s1, s2]

/-- The observed ratio, computed from the observed masses alone, matches `hazard_pT`. -/
example : obsEventMass (indepLaw pT pC) 1 / obsAtRiskMass (indepLaw pT pC) 1 = 1 / 3 := by
  rw [obsEventMass_indepLaw_values.2.1, obsAtRiskMass_indepLaw_values.2.1]
  norm_num

/-! ### Direct computation from a joint point-mass function -/

/-- The real mass of a set under a PMF on a finite type, as a finite sum of point masses. -/
theorem measureReal_eq_sum {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    p.toMeasure.real s = ∑ x ∈ univ.filter (· ∈ s), (p x).toReal := by
  have hs : p.toMeasure s = p.toMeasure ↑(univ.filter (· ∈ s)) := by
    congr 1; ext; simp
  rw [measureReal_def, hs, PMF.toMeasure_apply_finset,
    ENNReal.toReal_sum fun x _ => p.apply_ne_top x]

/-- The independent law of `pT` and `pC` written as a joint point-mass function, with weights
`P(T = t) P(C = c)`. -/
noncomputable def pTC : PMF (Fin 3 × Fin 3) :=
  PMF.ofFintype (fun ω => (((![1 / 4, 1 / 4, 1 / 2] : Fin 3 → ℝ≥0) ω.1 *
      (![1 / 2, 1 / 4, 1 / 4] : Fin 3 → ℝ≥0) ω.2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_three]
    norm_num)

/-- Cross-check of the rectangle factorization: summing the joint point masses over the observed
event set and the at-risk set directly gives `1/8` and `3/8` at `j = 1`, as in
`obsEventMass_indepLaw_values` and `obsAtRiskMass_indepLaw_values`. -/
theorem pTC_direct :
    obsEventMass pTC.toMeasure 1 = 1 / 8 ∧ obsAtRiskMass pTC.toMeasure 1 = 3 / 8 := by
  classical
  simp only [obsEventMass, obsAtRiskMass, measureReal_eq_sum]
  constructor <;>
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three, pTC] <;> norm_num

/-! ### No censoring before the horizon -/

/-- Censoring at the last grid point has survival mass `1` everywhere. -/
theorem survivalMass_pure_last {n : ℕ} (j : Fin (n + 1)) :
    survivalMass (PMF.pure (Fin.last n)) j = 1 := by
  rw [survivalMass, PMF.toMeasure_pure, measureReal_def,
    Measure.dirac_apply_of_mem (s := {t | j ≤ t}) (Fin.le_last j), ENNReal.toReal_one]

/-- Without censoring before the horizon, the observed event mass is the point mass of `T`. -/
example {n : ℕ} (p : PMF (Fin (n + 1))) (j : Fin (n + 1)) :
    obsEventMass (indepLaw p (PMF.pure (Fin.last n))) j = (p j).toReal := by
  rw [obsEventMass_indepLaw, survivalMass_pure_last, mul_one]

/-- Without censoring before the horizon, the observed ratio is the hazard of `T`. -/
example {n : ℕ} (p : PMF (Fin (n + 1))) (j : Fin (n + 1)) :
    obsEventMass (indepLaw p (PMF.pure (Fin.last n))) j /
      obsAtRiskMass (indepLaw p (PMF.pure (Fin.last n))) j = hazard p j :=
  obsEventMass_div_obsAtRiskMass _ _ _ (by rw [survivalMass_pure_last]; norm_num)

/-- Concrete instance: no censoring, `T ∼ pT`, hazard `1/3` at `j = 1`. -/
example : obsEventMass (indepLaw pT (PMF.pure (Fin.last 2))) 1 /
    obsAtRiskMass (indepLaw pT (PMF.pure (Fin.last 2))) 1 = 1 / 3 := by
  rw [obsEventMass_div_obsAtRiskMass _ _ _ (by rw [survivalMass_pure_last]; norm_num)]
  exact hazard_pT.2.1

/-- With censoring certain at time `0` and a tie-free event after `0`, nothing is observed past
`0`: the hypothesis `P(C ≥ j) ≠ 0` cannot be dropped. -/
example : obsEventMass (indepLaw pT (PMF.pure 0)) 1 = 0 ∧
    obsAtRiskMass (indepLaw pT (PMF.pure 0)) 1 = 0 := by
  have h : survivalMass (PMF.pure (0 : Fin 3)) 1 = 0 := by
    rw [survivalMass, PMF.toMeasure_pure, measureReal_def,
      Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
    simp
  rw [obsEventMass_indepLaw, obsAtRiskMass_indepLaw, h]
  simp

/-! ### Dependent censoring breaks identification -/

/-- A **dependent** joint law of `(T, C)` on `Fin 3 × Fin 3`: mass `1/4` at each of
`(0, 0)`, `(1, 1)`, `(2, 0)`, `(2, 2)`. Late events are often censored early. -/
noncomputable def qDep : PMF (Fin 3 × Fin 3) :=
  PMF.ofFintype (fun ω => ((![![1 / 4, 0, 0], ![0, 1 / 4, 0], ![1 / 4, 0, 1 / 4]] :
      Fin 3 → Fin 3 → ℝ≥0) ω.1 ω.2 : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_three]
    norm_num)

/-- The event-time marginal of `qDep` is `pT`, whose hazard at `1` is `1/3`. -/
theorem qDep_map_fst : qDep.map Prod.fst = pT := by
  have h4 : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ = 2⁻¹ :=
    (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).1 (by
      rw [ENNReal.toReal_add (by simp) (by simp)]; simp; norm_num)
  ext t
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  fin_cases t <;> simp [Fin.sum_univ_three, qDep, pT, h4]

/-- Under `qDep`, the observed masses at `1` are `1/4` and `1/2`, so the observed ratio is `1/2`,
not the hazard `1/3` of the event time. -/
theorem qDep_ratio :
    obsEventMass qDep.toMeasure 1 = 1 / 4 ∧ obsAtRiskMass qDep.toMeasure 1 = 1 / 2 ∧
      obsEventMass qDep.toMeasure 1 / obsAtRiskMass qDep.toMeasure 1 = 1 / 2 := by
  classical
  have hE : obsEventMass qDep.toMeasure 1 = 1 / 4 := by
    simp only [obsEventMass, measureReal_eq_sum]
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three, qDep]
  have hR : obsAtRiskMass qDep.toMeasure 1 = 1 / 2 := by
    simp only [obsAtRiskMass, measureReal_eq_sum]
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three, qDep]
    norm_num
  refine ⟨hE, hR, ?_⟩
  rw [hE, hR]
  norm_num

/-- **Dependent censoring breaks identification**: the observed ratio under `qDep` differs from the
hazard of its event-time marginal. -/
theorem qDep_ratio_ne_hazard :
    obsEventMass qDep.toMeasure 1 / obsAtRiskMass qDep.toMeasure 1 ≠
      hazard (qDep.map Prod.fst) 1 := by
  rw [qDep_ratio.2.2, qDep_map_fst, hazard_pT.2.1]
  norm_num

/-- Consequently `qDep` is not an independent censoring model with event-time law `pT`. -/
theorem qDep_ne_indepLaw (pC' : PMF (Fin 3)) : qDep.toMeasure ≠ indepLaw pT pC' := by
  intro h
  have hR : obsAtRiskMass (indepLaw pT pC') 1 ≠ 0 := by
    rw [← h, qDep_ratio.2.1]; norm_num
  have := obsEventMass_div_obsAtRiskMass_of_ne_zero pT pC' 1 hR
  rw [← h, qDep_ratio.2.2, hazard_pT.2.1] at this
  norm_num at this

/-- On `Fin 2 × Fin 2` only a degenerate counterexample exists (at `j = 0` both sides are
`P(T = 0)`, and at `j = 1` both are `1` once `P(X ≥ 1) > 0`): with `T = 1 ⇒ C = 0`, the observed
ratio at `1` is `0 / 0 = 0` while the hazard of `T` at `1` is `1`. -/
noncomputable def qDep₂ : PMF (Fin 2 × Fin 2) :=
  PMF.ofFintype (fun ω => ((![![0, 1 / 2], ![1 / 2, 0]] : Fin 2 → Fin 2 → ℝ≥0) ω.1 ω.2 : ℝ≥0∞))
    (by
      rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two]
      norm_num)

theorem qDep₂_ratio_ne_hazard :
    obsEventMass qDep₂.toMeasure 1 / obsAtRiskMass qDep₂.toMeasure 1 = 0 ∧
      hazard (qDep₂.map Prod.fst) 1 = 1 := by
  classical
  constructor
  · simp only [obsEventMass, obsAtRiskMass, measureReal_eq_sum]
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two, qDep₂]
  · simp only [hazard, survivalMass_eq_sum]
    simp [Finset.sum_filter, Fin.sum_univ_two, Fintype.sum_prod_type, qDep₂]

/-! ### Competing risks -/

/-- Two causes on `Fin 2`, uniform joint law of `(T, J)`. -/
noncomputable def pTJ : PMF (Fin 2 × Fin 2) :=
  PMF.ofFintype (fun _ => ((1 / 4 : ℝ≥0) : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one]
    simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    norm_num)

/-- The cause-specific hazard of cause `0` at time `1` is `(1/4) / (1/2) = 1/2`. -/
theorem causeHazard_pTJ : causeHazard pTJ 1 0 = 1 / 2 := by
  classical
  simp only [causeHazard, measureReal_eq_sum, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  simp [pTJ]
  norm_num

/-- With censoring at the horizon, the observed cause-`0` ratio at `1` is the cause-specific
hazard `1/2`. -/
example : causeEventMass (indepCauseLaw pTJ (PMF.pure (Fin.last 1))) 1 0 /
    causeAtRiskMass (indepCauseLaw pTJ (PMF.pure (Fin.last 1))) 1 = 1 / 2 := by
  rw [causeEventMass_div_obsAtRiskMass _ _ _ _ (by rw [survivalMass_pure_last]; norm_num),
    causeHazard_pTJ]

end MathlibExtTest.Probability.Statistics.Censoring

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import MathlibExt.Probability.Causality.ConfoundingEValue

namespace MathlibExt.Probability.Causality.ConfoundingRevalidationEvalue

open Convexity
open scoped BigOperators

private noncomputable def twoLevelLaw (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    StdSimplex ℝ (Fin 2) :=
  StdSimplex.duple 0 1 (sub_nonneg.mpr hq.2) hq.1 (sub_add_cancel 1 q)

private theorem sup_fin_two (f : Fin 2 → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty f = max (f 0) (f 1) := by
  have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp only [h]
  rfl

private theorem inf_fin_two (f : Fin 2 → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty f = min (f 0) (f 1) := by
  have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp only [h]
  rfl

private noncomputable def equalityModel : FiniteRiskModel 1 where
  exposureProb := 1 / 2
  exposureProb_mem := by norm_num [Set.mem_Ioo]
  confounderLaw e :=
    if e then twoLevelLaw 1 (by norm_num [Set.mem_Icc])
    else twoLevelLaw (1 / 2) (by norm_num [Set.mem_Icc])
  control_mass_pos u := by
    fin_cases u <;> norm_num [twoLevelLaw, StdSimplex.weights_duple]
  risk _ := ![1 / 4, 1 / 2]
  risk_mem e u := by
    fin_cases u <;> norm_num [Set.mem_Ioc, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem equal_risk_values :
    equalityModel.exposureConfounderRR = 2 ∧ equalityModel.confounderOutcomeRR = 2 ∧
    equalityModel.observedRR = 4 / 3 ∧ equalityModel.standardizedRR = 1 ∧
    equalityModel.confoundingRR = 4 / 3 := by
  have ht0 : equalityModel.mass true 0 = 0 := by
    norm_num [FiniteRiskModel.mass, equalityModel, twoLevelLaw, StdSimplex.weights_duple]
  have ht1 : equalityModel.mass true 1 = 1 := by
    norm_num [FiniteRiskModel.mass, equalityModel, twoLevelLaw, StdSimplex.weights_duple]
  have hf0 : equalityModel.mass false 0 = 1 / 2 := by
    norm_num [FiniteRiskModel.mass, equalityModel, twoLevelLaw, StdSimplex.weights_duple]
  have hf1 : equalityModel.mass false 1 = 1 / 2 := by
    norm_num [FiniteRiskModel.mass, equalityModel, twoLevelLaw, StdSimplex.weights_duple]
  have hEU : equalityModel.exposureConfounderRR = 2 := by
    rw [FiniteRiskModel.exposureConfounderRR, sup_fin_two]
    norm_num [ht0, ht1, hf0, hf1, max_def]
  have hUD (e : Bool) : equalityModel.armConfounderOutcomeRR e = 2 := by
    rw [FiniteRiskModel.armConfounderOutcomeRR, sup_fin_two, inf_fin_two]
    change max (1 / 4) (1 / 2) / min (1 / 4) (1 / 2) = (2 : ℝ)
    norm_num [max_def, min_def]
  have hObs : equalityModel.observedRR = 4 / 3 := by
    change (∑ u : Fin 2, equalityModel.risk true u * equalityModel.mass true u) /
      (∑ u : Fin 2, equalityModel.risk false u * equalityModel.mass false u) = 4 / 3
    simp only [Fin.sum_univ_two, ht0, ht1, hf0, hf1]
    change ((1 / 4) * 0 + (1 / 2) * 1) /
      ((1 / 4) * (1 / 2) + (1 / 2) * (1 / 2)) = (4 / 3 : ℝ)
    norm_num
  have hStd : equalityModel.standardizedRR = 1 := by
    unfold FiniteRiskModel.standardizedRR FiniteRiskModel.standardizedRisk
    exact div_self (equalityModel.standardizedRisk_pos false).ne'
  refine ⟨hEU, ?_, hObs, hStd, ?_⟩
  · simp [FiniteRiskModel.confounderOutcomeRR, hUD]
  · norm_num [FiniteRiskModel.confoundingRR, hObs, hStd]

private theorem sqrt_four_ninths :
    Real.sqrt ((4 / 3 : ℝ) * (4 / 3 - 1)) = 2 / 3 := by
  rw [show (4 / 3 : ℝ) * (4 / 3 - 1) = (2 / 3) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

private theorem evalue_four_thirds : confoundingEValue (4 / 3) = 2 := by
  unfold confoundingEValue
  rw [ite_eq_right (by norm_num)]
  dsimp only
  rw [sqrt_four_ninths]
  norm_num

private theorem evalue_reciprocal : confoundingEValue (3 / 4) = 2 := by
  unfold confoundingEValue
  rw [ite_eq_left (by norm_num), show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num]
  dsimp only
  rw [sqrt_four_ninths]
  norm_num

private theorem evalue_null : confoundingEValue 1 = 1 :=
  confoundingEValue_one

private theorem cornfield_high_threshold_client : (2 : ℝ) ≤ 2 := by
  obtain ⟨hx, hy, _, _, hc⟩ := equal_risk_values
  have h := equalityModel.cornfield_high_threshold (by rw [hc]; norm_num)
  exact Eq.mp (by rw [hc, evalue_four_thirds, hx, hy, max_self]) h

private theorem high_threshold_eq_ratio_client :
    (equalityModel.observedRR + Real.sqrt (equalityModel.observedRR *
      (equalityModel.observedRR - equalityModel.standardizedRR))) /
      equalityModel.standardizedRR = 2 := by
  obtain ⟨_, _, ho, hs, hc⟩ := equal_risk_values
  have h := equalityModel.high_threshold_eq_ratio (by rw [ho, hs]; norm_num)
  rw [hc, evalue_four_thirds] at h
  exact h.symm

private theorem confoundingEValue_le_max_client : (2 : ℝ) ≤ 2 := by
  obtain ⟨hx, hy, ho, hs, _⟩ := equal_risk_values
  have h := equalityModel.confoundingEValue_le_max (by rw [ho]; norm_num) hs
  exact Eq.mp (by rw [ho, evalue_four_thirds, hx, hy, max_self]) h

private theorem boundingFactor_eValue_client : confoundingBoundingFactor 2 2 = 4 / 3 := by
  have h := confoundingBoundingFactor_eValue (rr := 4 / 3) (by norm_num)
  rw [evalue_four_thirds] at h
  exact h

private theorem boundingFactor_attained_client :
    ∃ m : FiniteRiskModel 1, m.exposureProb = 1 / 3 ∧
      m.exposureConfounderRR = 3 ∧ m.confounderOutcomeRR = 4 ∧
      m.standardizedRR = 3 / 2 ∧ m.confoundingRR = 2 ∧ m.observedRR = 3 := by
  obtain ⟨m, hp, hx, hy, hs, hc⟩ := FiniteRiskModel.confoundingBoundingFactor_attained
    (x := 3) (y := 4) (p := 1 / 3) (β := 3 / 2)
    (by norm_num) (by norm_num) (by norm_num [Set.mem_Ioo]) (by norm_num)
  have hfactor : confoundingBoundingFactor 3 4 = 2 := by
    norm_num [confoundingBoundingFactor]
  rw [hfactor] at hc
  have ho : m.observedRR = 3 := by
    unfold FiniteRiskModel.confoundingRR at hc
    rw [hs] at hc
    have h := (div_eq_iff (by norm_num : (3 / 2 : ℝ) ≠ 0)).mp hc
    norm_num at h
    exact h
  exact ⟨m, hp, hx, hy, hs, hc, ho⟩

private theorem boundingFactor_one_left_client :
    ∃ m : FiniteRiskModel 1, m.exposureProb = 1 / 3 ∧
      0 < m.mass true 0 ∧ 0 < m.mass true 1 ∧
      m.exposureConfounderRR = 1 ∧ m.confounderOutcomeRR = 4 ∧
      m.standardizedRR = 3 / 2 ∧ m.confoundingRR = 1 := by
  obtain ⟨m, hp, hpos, hx, hy, hs, hc⟩ :=
    FiniteRiskModel.confoundingBoundingFactor_attained_one_left
      (y := 4) (p := 1 / 3) (β := 3 / 2)
      (by norm_num) (by norm_num [Set.mem_Ioo]) (by norm_num)
  have hfactor : confoundingBoundingFactor 1 4 = 1 := by
    norm_num [confoundingBoundingFactor]
  rw [hfactor] at hc
  exact ⟨m, hp, hpos 0, hpos 1, hx, hy, hs, hc⟩

private theorem boundingFactor_one_right_client :
    ∃ m : FiniteRiskModel 1, m.exposureProb = 1 / 3 ∧
      0 < m.mass true 0 ∧ 0 < m.mass true 1 ∧
      m.exposureConfounderRR = 3 ∧ m.confounderOutcomeRR = 1 ∧
      m.standardizedRR = 3 / 2 ∧ m.confoundingRR = 1 := by
  obtain ⟨m, hp, hpos, hx, hy, hs, hc⟩ :=
    FiniteRiskModel.confoundingBoundingFactor_attained_one_right
      (x := 3) (p := 1 / 3) (β := 3 / 2)
      (by norm_num) (by norm_num [Set.mem_Ioo]) (by norm_num)
  have hfactor : confoundingBoundingFactor 3 1 = 1 := by
    norm_num [confoundingBoundingFactor]
  rw [hfactor] at hc
  exact ⟨m, hp, hpos 0, hpos 1, hx, hy, hs, hc⟩

private theorem eValue_attained_client :
    ∃ m : FiniteRiskModel 1, m.exposureProb = 1 / 3 ∧
      m.observedRR = 4 / 3 ∧ m.standardizedRR = 1 ∧
      m.exposureConfounderRR = 2 ∧ m.confounderOutcomeRR = 2 := by
  obtain ⟨m, hp, ho, hs, hx, hy⟩ := FiniteRiskModel.confoundingEValue_attained
    (rr := 4 / 3) (p := 1 / 3) (by norm_num) (by norm_num [Set.mem_Ioo])
  rw [evalue_four_thirds] at hx hy
  exact ⟨m, hp, ho, hs, hx, hy⟩

#print axioms sup_fin_two
#print axioms inf_fin_two
#print axioms equal_risk_values
#print axioms sqrt_four_ninths
#print axioms evalue_four_thirds
#print axioms evalue_reciprocal
#print axioms evalue_null
#print axioms cornfield_high_threshold_client
#print axioms high_threshold_eq_ratio_client
#print axioms confoundingEValue_le_max_client
#print axioms boundingFactor_eValue_client
#print axioms boundingFactor_attained_client
#print axioms boundingFactor_one_left_client
#print axioms boundingFactor_one_right_client
#print axioms eValue_attained_client

end MathlibExt.Probability.Causality.ConfoundingRevalidationEvalue

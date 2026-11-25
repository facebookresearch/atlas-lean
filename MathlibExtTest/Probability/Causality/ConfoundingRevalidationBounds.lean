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
import MathlibExt.Probability.Causality.ConfoundingBounds

namespace MathlibExt.Probability.Causality.ConfoundingRevalidationBounds

open Convexity FiniteRiskModel
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

private noncomputable def positiveMass : FiniteRiskModel 1 where
  exposureProb := 1 / 2
  exposureProb_mem := by norm_num [Set.mem_Ioo]
  confounderLaw e :=
    if e then twoLevelLaw (4 / 5) (by norm_num [Set.mem_Icc])
    else twoLevelLaw (2 / 5) (by norm_num [Set.mem_Icc])
  control_mass_pos u := by
    fin_cases u <;> norm_num [twoLevelLaw, StdSimplex.weights_duple]
  risk e := if e then ![1 / 5, 1 / 2] else ![1 / 10, 3 / 10]
  risk_mem e u := by
    cases e <;> fin_cases u <;> norm_num [Set.mem_Ioc]

private theorem positive_masses (e : Bool) (u : Fin 2) :
    0 < positiveMass.mass e u := by
  cases e <;> fin_cases u <;>
    norm_num [mass, positiveMass, twoLevelLaw, StdSimplex.weights_duple]

private theorem positive_observed (e : Bool) :
    positiveMass.observedRisk e = if e then 11 / 25 else 9 / 50 := by
  change (∑ u : Fin 2, positiveMass.risk e u * positiveMass.mass e u) = _
  rw [Fin.sum_univ_two]
  cases e <;> norm_num [mass, positiveMass, twoLevelLaw, StdSimplex.weights_duple]

private theorem positive_standardized (e : Bool) :
    positiveMass.standardizedRisk e = if e then 19 / 50 else 11 / 50 := by
  change (∑ u : Fin 2, positiveMass.risk e u * positiveMass.marginalMass u) = _
  rw [Fin.sum_univ_two]
  cases e <;> norm_num [marginalMass, mass, positiveMass, twoLevelLaw,
    StdSimplex.weights_duple]

private theorem positive_observedRR : positiveMass.observedRR = 22 / 9 := by
  norm_num [observedRR, positive_observed]

private theorem positive_standardizedRR : positiveMass.standardizedRR = 19 / 11 := by
  norm_num [standardizedRR, positive_standardized]

private theorem positive_armRR (e : Bool) :
    positiveMass.armStandardizedRR e = if e then 22 / 13 else 16 / 9 := by
  change (∑ u : Fin 2, positiveMass.risk true u * positiveMass.mass e u) /
    (∑ u : Fin 2, positiveMass.risk false u * positiveMass.mass e u) = _
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  cases e <;> norm_num [mass, positiveMass, twoLevelLaw, StdSimplex.weights_duple]

theorem arm_ratios_differ :
    positiveMass.armStandardizedRR true ≠ positiveMass.armStandardizedRR false := by
  norm_num [positive_armRR]

theorem arm_ratio_treated_client : positiveMass.armConfoundingRR true = 13 / 9 := by
  rw [positiveMass.armConfoundingRR_eq_ratio true]
  change (∑ u : Fin 2, positiveMass.risk false u * positiveMass.mass true u) /
    (∑ u : Fin 2, positiveMass.risk false u * positiveMass.mass false u) = 13 / 9
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [mass, positiveMass, twoLevelLaw, StdSimplex.weights_duple]

theorem arm_ratio_control_client : positiveMass.armConfoundingRR false = 11 / 8 := by
  rw [positiveMass.armConfoundingRR_eq_ratio false]
  change (∑ u : Fin 2, positiveMass.risk true u * positiveMass.mass true u) /
    (∑ u : Fin 2, positiveMass.risk true u * positiveMass.mass false u) = 11 / 8
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [mass, positiveMass, twoLevelLaw, StdSimplex.weights_duple]

private theorem positive_weight : positiveMass.standardizationWeight = 13 / 22 := by
  unfold standardizationWeight
  rw [positive_standardized]
  change (1 / 2) * (∑ u : Fin 2, positiveMass.risk false u * positiveMass.mass true u) /
    (11 / 50) = 13 / 22
  rw [Fin.sum_univ_two]
  norm_num [mass, positiveMass, twoLevelLaw, StdSimplex.weights_duple]

theorem weighted_standardized_client :
    (19 / 11 : ℝ) = (13 / 22) * (22 / 13) + (1 - 13 / 22) * (16 / 9) := by
  simpa only [positive_standardizedRR, positive_weight, positive_armRR,
    Bool.false_eq_true, ↓reduceIte] using positiveMass.standardizedRR_eq_weighted

private theorem positive_confoundingRR : positiveMass.confoundingRR = 242 / 171 := by
  norm_num [confoundingRR, positive_observedRR, positive_standardizedRR]

theorem weighted_reciprocal_client :
    (171 / 242 : ℝ) = (13 / 22) / (13 / 9) + (1 - 13 / 22) / (11 / 8) := by
  have h := positiveMass.inv_confoundingRR_eq_weighted
  rw [positive_confoundingRR, positive_weight, arm_ratio_treated_client,
    arm_ratio_control_client] at h
  convert h using 1; norm_num

theorem weight_membership_client : (13 / 22 : ℝ) ∈ Set.Icc 0 1 := by
  simpa only [positive_weight] using positiveMass.standardizationWeight_mem

theorem weight_strict_interior : positiveMass.standardizationWeight ∈ Set.Ioo 0 1 := by
  norm_num [positive_weight, Set.mem_Ioo]

private theorem positive_exposure : positiveMass.exposureConfounderRR = 2 := by
  rw [exposureConfounderRR, sup_fin_two]
  norm_num [mass, positiveMass, twoLevelLaw, StdSimplex.weights_duple, max_def]

private theorem positive_outcome_arm (e : Bool) :
    positiveMass.armConfounderOutcomeRR e = if e then 5 / 2 else 3 := by
  rw [armConfounderOutcomeRR, sup_fin_two, inf_fin_two]
  cases e <;> norm_num [positiveMass, max_def, min_def]

private theorem positive_outcome : positiveMass.confounderOutcomeRR = 3 := by
  norm_num [confounderOutcomeRR, positive_outcome_arm, max_def]

private theorem positive_factor :
    confoundingBoundingFactor positiveMass.exposureConfounderRR
      positiveMass.confounderOutcomeRR = 3 / 2 := by
  norm_num [positive_exposure, positive_outcome, confoundingBoundingFactor]

theorem strict_left_client : confoundingBoundingFactor 2 2 < confoundingBoundingFactor 3 2 :=
  confoundingBoundingFactor_strictMonoOn_left (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ∈ Set.Ioi 1) (by norm_num : (3 : ℝ) ∈ Set.Ioi 1)
    (by norm_num : (2 : ℝ) < 3)

theorem strict_right_client : confoundingBoundingFactor 2 2 < confoundingBoundingFactor 2 3 :=
  confoundingBoundingFactor_strictMonoOn_right (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ∈ Set.Ioi 1) (by norm_num : (3 : ℝ) ∈ Set.Ioi 1)
    (by norm_num : (2 : ℝ) < 3)

theorem boundary_min_client : confoundingBoundingFactor 1 3 ≤ min 1 3 :=
  confoundingBoundingFactor_le_min (by norm_num) (by norm_num)

theorem strict_min_client : confoundingBoundingFactor 2 3 < min 2 3 :=
  confoundingBoundingFactor_lt_min (by norm_num) (by norm_num)

theorem arm_bound_treated_client : (13 / 9 : ℝ) ≤ 3 / 2 := by
  have h := positiveMass.armConfoundingRR_le_boundingFactor true
  rw [arm_ratio_treated_client, positive_exposure, Bool.not_true,
    positive_outcome_arm] at h
  convert h using 1; norm_num [confoundingBoundingFactor]

theorem arm_bound_control_client : (11 / 8 : ℝ) ≤ 10 / 7 := by
  have h := positiveMass.armConfoundingRR_le_boundingFactor false
  rw [arm_ratio_control_client, positive_exposure, Bool.not_false,
    positive_outcome_arm] at h
  convert h using 1; norm_num [confoundingBoundingFactor]

theorem common_factor_control_client : confoundingBoundingFactor 2 3 ≤ 3 / 2 := by
  have h := positiveMass.armBoundingFactor_le_boundingFactor false
  rw [positive_factor] at h
  simpa only [positive_exposure, positive_outcome_arm, Bool.false_eq_true, ↓reduceIte] using h

theorem common_factor_treated_client : (10 / 7 : ℝ) ≤ 3 / 2 := by
  have h := positiveMass.armBoundingFactor_le_boundingFactor true
  rw [positive_factor, positive_exposure, positive_outcome_arm] at h
  convert h using 1; norm_num [confoundingBoundingFactor]

theorem population_bound_client : (242 / 171 : ℝ) ≤ 3 / 2 := by
  have h := positiveMass.confoundingRR_le_boundingFactor
  rw [positive_observedRR, positive_standardizedRR, positive_factor] at h
  convert h using 1; norm_num

theorem divided_bound_client : (44 / 27 : ℝ) ≤ 19 / 11 := by
  have h := positiveMass.observedRR_div_boundingFactor_le_standardizedRR
  rw [positive_observedRR, positive_standardizedRR, positive_factor] at h
  convert h using 1; norm_num

private noncomputable def equalRisk : FiniteRiskModel 1 where
  exposureProb := 1 / 2
  exposureProb_mem := by norm_num [Set.mem_Ioo]
  confounderLaw e :=
    if e then twoLevelLaw 1 (by norm_num [Set.mem_Icc])
    else twoLevelLaw (1 / 2) (by norm_num [Set.mem_Icc])
  control_mass_pos u := by
    fin_cases u <;> norm_num [twoLevelLaw, StdSimplex.weights_duple]
  risk _ := ![1 / 4, 1 / 2]
  risk_mem e u := by
    fin_cases u <;> norm_num [Set.mem_Ioc]

private theorem equal_observedRR : equalRisk.observedRR = 4 / 3 := by
  change (∑ u : Fin 2, equalRisk.risk true u * equalRisk.mass true u) /
    (∑ u : Fin 2, equalRisk.risk false u * equalRisk.mass false u) = 4 / 3
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [mass, equalRisk, twoLevelLaw, StdSimplex.weights_duple]

private theorem equal_standardizedRR : equalRisk.standardizedRR = 1 := by
  unfold standardizedRR standardizedRisk
  exact div_self (equalRisk.standardizedRisk_pos false).ne'

private theorem equal_exposure : equalRisk.exposureConfounderRR = 2 := by
  rw [exposureConfounderRR, sup_fin_two]
  norm_num [mass, equalRisk, twoLevelLaw, StdSimplex.weights_duple, max_def]

private theorem equal_outcome_arm (e : Bool) : equalRisk.armConfounderOutcomeRR e = 2 := by
  rw [armConfounderOutcomeRR, sup_fin_two, inf_fin_two]
  norm_num [equalRisk, max_def, min_def]

private theorem equal_outcome : equalRisk.confounderOutcomeRR = 2 := by
  norm_num [confounderOutcomeRR, equal_outcome_arm]

theorem equal_factor :
    confoundingBoundingFactor equalRisk.exposureConfounderRR
      equalRisk.confounderOutcomeRR = 4 / 3 := by
  norm_num [equal_exposure, equal_outcome, confoundingBoundingFactor]

theorem equal_null_cell : equalRisk.mass true 0 = 0 ∧ 0 < equalRisk.risk true 0 := by
  norm_num [mass, equalRisk, twoLevelLaw, StdSimplex.weights_duple]

theorem required_strict_premise :
    equalRisk.observedRR < equalRisk.exposureConfounderRR * equalRisk.standardizedRR := by
  norm_num [equal_observedRR, equal_exposure, equal_standardizedRR]

theorem required_strength_value :
    (equalRisk.exposureConfounderRR * equalRisk.observedRR - equalRisk.observedRR) /
      (equalRisk.exposureConfounderRR * equalRisk.standardizedRR - equalRisk.observedRR) = 2 := by
  norm_num [equal_exposure, equal_observedRR, equal_standardizedRR]

theorem required_strength_client : (2 : ℝ) ≤ 2 := by
  simpa only [required_strength_value, equal_outcome] using
    equalRisk.required_confounderOutcomeRR required_strict_premise

theorem low_threshold_client : (242 / 171 : ℝ) ≤ min 2 3 := by
  simpa only [positive_confoundingRR, positive_exposure, positive_outcome] using
    positiveMass.cornfield_low_threshold

private noncomputable def swapped : FiniteRiskModel 1 where
  exposureProb := 1 - positiveMass.exposureProb
  exposureProb_mem := by norm_num [positiveMass, Set.mem_Ioo]
  confounderLaw e := positiveMass.confounderLaw (!e)
  control_mass_pos u := positive_masses true u
  risk e := positiveMass.risk (!e)
  risk_mem e u := positiveMass.risk_mem (!e) u

private theorem swapped_observedRR : swapped.observedRR = 9 / 22 := by
  change positiveMass.observedRisk false / positiveMass.observedRisk true = 9 / 22
  norm_num [positive_observed]

private theorem swapped_standardizedRR : swapped.standardizedRR = 11 / 19 := by
  change (∑ u : Fin 2, swapped.risk true u * swapped.marginalMass u) /
    (∑ u : Fin 2, swapped.risk false u * swapped.marginalMass u) = 11 / 19
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [marginalMass, mass, swapped, positiveMass, twoLevelLaw, StdSimplex.weights_duple]

private theorem swapped_outcome : swapped.confounderOutcomeRR = 3 := by
  change max (positiveMass.armConfounderOutcomeRR false)
    (positiveMass.armConfounderOutcomeRR true) = 3
  norm_num [positive_outcome_arm, max_def]

theorem swapped_exposed_positive (u : Fin 2) : 0 < swapped.mass true u :=
  positive_masses false u

private theorem swapped_reverse_exposure :
    Finset.univ.sup' Finset.univ_nonempty
      (fun u => swapped.mass false u / swapped.mass true u) = 2 := by
  change positiveMass.exposureConfounderRR = 2
  exact positive_exposure

theorem preventive_bound_client : (11 / 19 : ℝ) ≤ 27 / 44 := by
  have h := swapped.standardizedRR_le_observedRR_mul_boundingFactor swapped_exposed_positive
  rw [swapped_standardizedRR, swapped_observedRR, swapped_reverse_exposure,
    swapped_outcome] at h
  convert h using 1; norm_num [confoundingBoundingFactor]

theorem equal_risks : equalRisk.risk true = equalRisk.risk false := rfl

theorem higher_level_one : equalRisk.risk false 0 < equalRisk.risk false 1 := by
  norm_num [equalRisk]

theorem observed_above_one : 1 < equalRisk.observedRR := by
  norm_num [equal_observedRR]

theorem binary_cornfield_client : (4 / 3 : ℝ) < 2 := by
  have h := FiniteRiskModel.cornfield_binary equal_risks higher_level_one observed_above_one
  rw [equal_observedRR] at h
  convert h using 1; norm_num [mass, equalRisk, twoLevelLaw, StdSimplex.weights_duple]

#print axioms arm_ratio_treated_client
#print axioms arm_ratio_control_client
#print axioms weighted_standardized_client
#print axioms weighted_reciprocal_client
#print axioms weight_membership_client
#print axioms strict_left_client
#print axioms strict_right_client
#print axioms boundary_min_client
#print axioms strict_min_client
#print axioms arm_bound_treated_client
#print axioms arm_bound_control_client
#print axioms common_factor_control_client
#print axioms common_factor_treated_client
#print axioms population_bound_client
#print axioms divided_bound_client
#print axioms required_strength_client
#print axioms low_threshold_client
#print axioms preventive_bound_client
#print axioms binary_cornfield_client

end MathlibExt.Probability.Causality.ConfoundingRevalidationBounds

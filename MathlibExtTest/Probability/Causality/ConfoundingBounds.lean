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

/-! # Finite confounding checks -/

namespace MathlibExt.Probability.Causality

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

private theorem sharpness_at_two :
    equalityModel.exposureConfounderRR = 2 ∧ equalityModel.confounderOutcomeRR = 2 ∧
    equalityModel.observedRR = 4 / 3 ∧ equalityModel.standardizedRR = 1 ∧
    equalityModel.confoundingRR = confoundingBoundingFactor 2 2 := by
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
  · norm_num [FiniteRiskModel.confoundingRR, hObs, hStd, confoundingBoundingFactor]

private theorem equality_witness_has_exposed_null_cell :
    equalityModel.mass true 0 = 0 ∧ equalityModel.jointMass true 0 true = 0 ∧
    0 < equalityModel.marginalMass 0 ∧ 0 < equalityModel.risk true 0 := by
  norm_num [FiniteRiskModel.mass, FiniteRiskModel.jointMass, FiniteRiskModel.marginalMass,
    FiniteRiskModel.armProb, equalityModel, twoLevelLaw, StdSimplex.weights_duple,
    Matrix.cons_val_zero]

private theorem confoundingEValue_four_thirds :
    confoundingEValue (4 / 3) = 2 ∧ confoundingEValue (3 / 4) = 2 := by
  have hs : Real.sqrt (4 / 3 * (4 / 3 - 1)) = 2 / 3 := by
    rw [show (4 / 3 : ℝ) * (4 / 3 - 1) = (2 / 3) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  unfold confoundingEValue
  rw [ite_eq_right (by norm_num), ite_eq_left (by norm_num),
    show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num]
  dsimp only
  rw [hs]
  norm_num

private noncomputable def singleLevelModel : FiniteRiskModel 0 where
  exposureProb := 1 / 2
  exposureProb_mem := by norm_num [Set.mem_Ioo]
  confounderLaw _ := StdSimplex.single 0
  control_mass_pos u := by
    change 0 < (StdSimplex.single (R := ℝ) (0 : Fin 1)).weights u
    rw [StdSimplex.weights_apply_eq_one]
    exact zero_lt_one
  risk _ _ := 1
  risk_mem e u := by norm_num [Set.mem_Ioc]

private theorem single_level_unit_parameters :
    singleLevelModel.exposureConfounderRR = 1 ∧ singleLevelModel.confounderOutcomeRR = 1 ∧
    singleLevelModel.confoundingRR = 1 := by
  let : Subsingleton (Fin (0 + 1)) := by
    change Subsingleton (Fin 1)
    infer_instance
  have hMass (e : Bool) (u : Fin (0 + 1)) : singleLevelModel.mass e u = 1 :=
    StdSimplex.weights_apply_eq_one _ _
  constructor
  · simp [FiniteRiskModel.exposureConfounderRR, hMass]
  constructor
  · simp [FiniteRiskModel.confounderOutcomeRR, FiniteRiskModel.armConfounderOutcomeRR,
      singleLevelModel]
  have hObs (e : Bool) : singleLevelModel.observedRisk e = 1 := by
    simp only [FiniteRiskModel.observedRisk, hMass, mul_one]
    change (∑ _u : Fin 1, (1 : ℝ)) = 1
    simp
  have hStd : singleLevelModel.standardizedRR = 1 := by
    unfold FiniteRiskModel.standardizedRR FiniteRiskModel.standardizedRisk
    exact div_self (singleLevelModel.standardizedRisk_pos false).ne'
  simp [FiniteRiskModel.confoundingRR, FiniteRiskModel.observedRR, hStd, hObs]

end MathlibExt.Probability.Causality

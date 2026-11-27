/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Demography.FiniteLifeTable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Finite life-table probability examples -/

open Domains.Biology.Demography MeasureTheory FiniteLifeTable

noncomputable section

private def cohort : FiniteLifeTable 3 where
  survivors := ![15 / 2, 9 / 2, 9 / 2, 3 / 2]
  antitone := by
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    fin_cases i <;> norm_num
  final_nonneg := by norm_num [Fin.last]
  initial_pos := by norm_num

-- The flat second interval has zero probability, even though its risk set is positive.
example : (cohort.law (1 : Fin 3).castSucc).toReal = 0 := by
  rw [law_death]
  norm_num [cohort]

-- Death at 3 is the outcome at index 2, not the residual survivor at index 3.
example : cohort.law.toMeasure.real {i | i.val + 1 ∈ Set.Ioc 2 3} = 2 / 5 := by
  have h : {i : Fin 4 | i.val + 1 ∈ Set.Ioc 2 3} = {(2 : Fin 3).castSucc} := by
    ext i; fin_cases i <;> decide
  rw [h, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), law_death]
  norm_num [cohort]

private theorem terminalEvent : survives (3 : Fin 4) = {Fin.last 3} := by
  ext i
  change 3 < i.val + 1 ↔ i = Fin.last 3
  fin_cases i <;> decide

-- Strict survival through 3 leaves only the residual atom. Compute its mass as a singleton.
example : cohort.law.toMeasure.real (survives 3) = 1 / 5 := by
  rw [terminalEvent, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    law_residual]
  norm_num [cohort, Fin.last]

-- Compute the conditional probability directly from the four atoms, without the ratio theorem.
example : (ProbabilityTheory.cond cohort.law.toMeasure (survives 1)).real (survives 3) = 1 / 3 := by
  have h₁ : survives (1 : Fin 4) = ↑({1, 2, 3} : Finset (Fin 4)) := by
    ext i
    change 1 < i.val + 1 ↔ i ∈ ({1, 2, 3} : Finset (Fin 4))
    fin_cases i <;> decide
  have h₃₁ : survives (3 : Fin 4) ⊆ survives 1 := fun _ hi ↦ lt_trans (by decide : 1 < 3) hi
  rw [measureReal_def, ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet,
    Set.inter_eq_right.mpr h₃₁, h₁, terminalEvent, PMF.toMeasure_apply_finset,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  have c₁ : cohort.count 1 = 0 := by change 9 / 2 - 9 / 2 = (0 : ℝ); norm_num
  have c₂ : cohort.count 2 = 3 := by change 9 / 2 - 3 / 2 = (3 : ℝ); norm_num
  have c₃ : cohort.count 3 = 3 / 2 := rfl
  norm_num [law, c₁, c₂, c₃, show Fin.last 3 = 3 by decide,
    show cohort.survivors 0 = 15 / 2 by rfl, ENNReal.toReal_add]

-- Exercise the general ratio theorem on the same nontrivial conditional probability.
example : (ProbabilityTheory.cond cohort.law.toMeasure (survives 1)).real (survives 3) = 1 / 3 :=
  (cond_survives cohort 1 2 (by decide) (by norm_num [cohort])).trans (by norm_num [cohort])

-- Conditioning at the last date on positive survival and looking zero years ahead gives one.
example : (ProbabilityTheory.cond cohort.law.toMeasure (survives 3)).real (survives 3) = 1 :=
  (cond_survives cohort 3 0 (by decide) (by norm_num [cohort])).trans (by norm_num [cohort])

private def exhausted : FiniteLifeTable 1 where
  survivors := ![1, 0]
  antitone := by apply Fin.antitone_iff_succ_le.mpr; intro i; fin_cases i; norm_num
  final_nonneg := by norm_num [Fin.last]
  initial_pos := by norm_num

-- Extinction makes strict terminal survival zero, without conditioning on that null event.
example : exhausted.law.toMeasure.real (survives 1) = 0 := by
  rw [prob_survives]
  norm_num [exhausted]

private def newborn : FiniteLifeTable 0 where
  survivors := fun _ ↦ 7 / 2
  antitone := antitone_const
  final_nonneg := by norm_num
  initial_pos := by norm_num

-- An empty list of death intervals leaves all probability on the residual outcome.
example : newborn.law.toMeasure.real {Fin.last 0} = 1 := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), law_residual]
  norm_num [newborn]

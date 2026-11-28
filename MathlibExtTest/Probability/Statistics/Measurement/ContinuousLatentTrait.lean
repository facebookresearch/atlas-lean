/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.ProbabilityMassFunction.Uniform
import MathlibExt.Probability.Statistics.Measurement.ContinuousLatentTrait
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.NormNum

/-! # Regression tests for continuous latent-trait models -/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.Measurement

private noncomputable def classLaw : PMF Bool := PMF.uniformFintype Bool

private def classAbility (z : Bool) : ℝ := if z then 1 else -1

private theorem measurable_classAbility : Measurable classAbility := Measurable.of_discrete

private noncomputable def twoClassModel : ContinuousLatentTrait (Fin 2) where
  ability := ⟨classLaw.toMeasure.map classAbility,
    (Measure.isProbabilityMeasure_map_iff measurable_classAbility.aemeasurable).2 inferInstance⟩
  curve _ θ := if θ ≤ 0 then 0 else 1
  measurable_curve _ :=
    Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  curve_nonneg _ θ := by split_ifs <;> norm_num
  curve_le_one _ θ := by split_ifs <;> norm_num

-- The mixture puts equal mass on the two diagonal patterns and zero on a mixed pattern.
-- Both items are marginally fair, but the joint true mass is 1 / 2 rather than 1 / 4.
example : twoClassModel.responseLaw.real {fun _ => true} = 1 / 2 ∧
    twoClassModel.responseLaw.real {fun i => i == 0} = 0 ∧
    twoClassModel.responseLaw.real {fun _ => false} = 1 / 2 := by
  classical
  have h := twoClassModel.responseLaw_eq_finite_mixture classLaw classAbility
    measurable_classAbility rfl
  rw [h]
  simp only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.bind_apply, tsum_fintype, Fintype.sum_bool, classLaw, PMF.uniformFintype_apply,
    Fintype.card_bool]
  norm_num [ContinuousLatentTrait.responsePMF, localIndepPMF_apply, twoClassModel,
    classAbility, Fin.prod_univ_two]

-- The real singleton formula reduces the ability integral to its value at a point mass.
example (θ : ℝ) :
    let M : ContinuousLatentTrait (Fin 2) :=
      { ability := ⟨Measure.dirac θ, inferInstance⟩
        curve := fun _ _ => 1 / 4
        measurable_curve := fun _ => measurable_const
        curve_nonneg := fun _ _ => by norm_num
        curve_le_one := fun _ _ => by norm_num }
    M.responseLaw.real {fun _ => true} = 1 / 16 := by
  intro M
  rw [M.responseLaw_real_singleton]
  norm_num [M, Fin.prod_univ_two]

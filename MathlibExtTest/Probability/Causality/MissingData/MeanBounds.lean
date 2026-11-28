/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Causality.MissingData.MeanBounds
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality.MissingData
open scoped ENNReal

set_option quotPrecheck false in
local notation "obsRY" => fun z : Bool × ℝ => (z.1, if z.1 then z.2 else (0 : ℝ))

private def compatible (P : Measure (Bool × ℝ)) (a b : ℝ) : Set ℝ :=
  {m | ∃ Q : Measure (Bool × ℝ), IsProbabilityMeasure Q ∧
    (∀ᵐ z ∂Q, z.2 ∈ Set.Icc a b) ∧ Q.map obsRY = P.map obsRY ∧ (∫ z, z.2 ∂Q) = m}

private theorem range_constOutcome {a b : ℝ} (h : (1 : ℝ) ∈ Set.Icc a b) :
    ∀ᵐ z ∂constOutcomeLaw, z.2 ∈ Set.Icc a b := by
  have hm : MeasurableSet {z : Bool × ℝ | z.2 ∈ Set.Icc a b} := measurable_snd measurableSet_Icc
  rw [constOutcomeLaw, Measure.ae_ennreal_smul_measure_iff (by norm_num : (2⁻¹ : ENNReal) ≠ 0),
    ae_add_measure_iff, ae_dirac_iff hm, ae_dirac_iff hm]
  exact ⟨h, h⟩

private theorem half_response : constOutcomeLaw.real {z : Bool × ℝ | z.1 = true} = 1 / 2 := by
  norm_num [constOutcomeLaw, Measure.real, Measure.dirac_apply, ENNReal.toReal_inv]

private theorem half_observed_contribution : (∫ z, z.2 ∂(constOutcomeLaw.map obsRY)) = 1 / 2 := by
  rw [integral_map measurable_obsRY.aemeasurable measurable_snd.aestronglyMeasurable,
    constOutcomeLaw, integral_smul_measure,
    integral_add_measure (integrable_dirac eNorm_lt_top) (integrable_dirac eNorm_lt_top),
    integral_dirac, integral_dirac]
  norm_num [ENNReal.toReal_inv]

-- With half the outcomes observed at 1 and the range [0, 2], both endpoints and every interior
-- point are compatible, and no value outside the interval is compatible.
example : compatible constOutcomeLaw 0 2 = Set.Icc (1 / 2) (3 / 2) := by
  have h := missingOutcomeMean_identifiedSet_eq_Icc constOutcomeLaw
    (range_constOutcome (a := 0) (b := 2) (by norm_num [Set.mem_Icc]))
  change compatible constOutcomeLaw 0 2 = _ at h
  rw [half_response, half_observed_contribution] at h
  norm_num at h ⊢
  exact h

-- No responses: the entire known range stays compatible.
example : compatible (Measure.dirac (false, (1 : ℝ))) 0 2 = Set.Icc 0 2 := by
  let P := Measure.dirac (false, (1 : ℝ))
  have h := missingOutcomeMean_identifiedSet_eq_Icc P (a := 0) (b := 2)
    ((ae_dirac_iff (measurable_snd measurableSet_Icc)).2 (by norm_num [Set.mem_Icc]))
  change compatible P 0 2 = _ at h
  simpa [P, Measure.real, Measure.dirac_apply, Measure.map_dirac' measurable_obsRY] using h

-- All responses: the compatible means form a singleton, without restricting the model class
-- for missingness by positivity assumptions.
example : compatible (Measure.dirac (true, (1 : ℝ))) 0 2 = Set.Icc 1 1 := by
  let P := Measure.dirac (true, (1 : ℝ))
  have h := missingOutcomeMean_identifiedSet_eq_Icc P (a := 0) (b := 2)
    ((ae_dirac_iff (measurable_snd measurableSet_Icc)).2 (by norm_num [Set.mem_Icc]))
  change compatible P 0 2 = _ at h
  simpa [P, Measure.real, Measure.dirac_apply, Measure.map_dirac' measurable_obsRY] using h

-- A singleton outcome range also identifies the mean despite nonresponse.
example : compatible constOutcomeLaw 1 1 = Set.Icc 1 1 := by
  have h := missingOutcomeMean_identifiedSet_eq_Icc constOutcomeLaw
    (range_constOutcome ⟨le_rfl, le_rfl⟩)
  change compatible constOutcomeLaw 1 1 = _ at h
  rw [half_response, half_observed_contribution] at h
  norm_num at h ⊢
  exact h

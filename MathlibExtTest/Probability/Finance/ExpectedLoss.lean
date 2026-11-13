/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.ExpectedLoss

/-! # Tests for `MathlibExt.Probability.Finance.ExpectedLoss` -/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Finance.ExpectedLoss

namespace MathlibExtTest.ExpectedLoss

section Examples

theorem measure_real_univ_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.real Set.univ = 1 := by
  rw [MeasureTheory.Measure.real_def, measure_univ, ENNReal.toReal_one]

theorem expectedLoss_univ
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (EAD LGD : Ω → ℝ)
    (hInt : IntegrableOn (fun ω => EAD ω * LGD ω) Set.univ μ) :
    expectedLoss μ Set.univ EAD LGD = ∫ ω, EAD ω * LGD ω ∂μ := by
  have hμU : μ Set.univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  have hdecomp := expectedLoss_eq_defaultProbability_mul_conditionalExpectedLoss
    μ MeasurableSet.univ hμU hInt
  have hprob : defaultProbability μ Set.univ = 1 := by
    unfold defaultProbability
    exact measure_real_univ_eq_one μ
  have hcond : ProbabilityTheory.cond μ Set.univ = μ :=
    ProbabilityTheory.cond_univ μ
  unfold conditionalExpectedLoss at hdecomp
  rw [hcond, hprob, one_mul] at hdecomp
  exact hdecomp

theorem expectedLoss_const_univ
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    expectedLoss μ Set.univ (fun _ => 100) (fun _ => 0.4) = 40 := by
  have hInt : IntegrableOn (fun ω : Ω => (100:ℝ) * 0.4) Set.univ μ :=
    (MeasureTheory.integrable_const ((100:ℝ) * 0.4)).integrableOn
  rw [expectedLoss_univ μ (fun _ => 100) (fun _ => 0.4) hInt]
  have hval : (∫ ω : Ω, (100:ℝ) * 0.4 ∂μ) = 40 := by
    rw [MeasureTheory.integral_const, measure_real_univ_eq_one μ, one_smul]
    norm_num
  exact hval

private noncomputable def boolMeasure : Measure Bool :=
  ENNReal.ofReal (1/4 : ℝ) • Measure.dirac (true : Bool) +
    ENNReal.ofReal (3/4 : ℝ) • Measure.dirac (false : Bool)

private def boolDefault : Set Bool := {true}

private def boolEAD : Bool → ℝ := fun _ => 100

private noncomputable def boolLGD : Bool → ℝ := fun _ => (2/5 : ℝ)

private theorem bool_dirac_true_univ :
    (Measure.dirac (true : Bool)) Set.univ = 1 := by
  have hmem : (true : Bool) ∈ Set.univ := Set.mem_univ (true : Bool)
  rw [Measure.dirac_apply (true : Bool) Set.univ, Set.indicator_of_mem hmem]
  simp

private theorem bool_dirac_false_univ :
    (Measure.dirac (false : Bool)) Set.univ = 1 := by
  have hmem : (false : Bool) ∈ Set.univ := Set.mem_univ (false : Bool)
  rw [Measure.dirac_apply (false : Bool) Set.univ, Set.indicator_of_mem hmem]
  simp

private theorem bool_dirac_true_single :
    (Measure.dirac (true : Bool)) ({true} : Set Bool) = 1 := by
  have hmem : (true : Bool) ∈ ({true} : Set Bool) := by
    simp [Set.mem_singleton_iff]
  rw [Measure.dirac_apply (true : Bool) ({true} : Set Bool),
    Set.indicator_of_mem hmem]
  simp

private theorem bool_dirac_false_single :
    (Measure.dirac (false : Bool)) ({true} : Set Bool) = 0 := by
  have hnem : (false : Bool) ∉ ({true} : Set Bool) := by
    simp [Set.mem_singleton_iff]
  rw [Measure.dirac_apply (false : Bool) ({true} : Set Bool),
    Set.indicator_of_notMem hnem]

private theorem boolMeasure_univ : boolMeasure Set.univ = 1 := by
  simp only [boolMeasure, Measure.add_apply, Measure.smul_apply,
    bool_dirac_true_univ, bool_dirac_false_univ]
  simp only [smul_eq_mul, mul_one]
  have hadd : ENNReal.ofReal (1/4 : ℝ) + ENNReal.ofReal (3/4 : ℝ) =
      ENNReal.ofReal (1 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [hadd, ENNReal.ofReal_one]

private instance : IsProbabilityMeasure boolMeasure where
  measure_univ := boolMeasure_univ

private theorem boolMeasure_default :
    boolMeasure boolDefault = ENNReal.ofReal (1/4 : ℝ) := by
  simp only [boolMeasure, boolDefault, Measure.add_apply, Measure.smul_apply,
    bool_dirac_true_single, bool_dirac_false_single]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero]

private theorem boolDefault_measurable : MeasurableSet boolDefault := by
  simp only [boolDefault]
  exact measurableSet_singleton (true : Bool)

private theorem boolDefault_ne_univ : boolDefault ≠ Set.univ := by
  intro h
  have hfalse : (false : Bool) ∈ boolDefault := by
    rw [h]
    exact Set.mem_univ (false : Bool)
  simp only [boolDefault, Set.mem_singleton_iff] at hfalse
  have hne : (false : Bool) ≠ true := by decide
  exact hne hfalse

private theorem boolDefault_ne_empty : boolDefault ≠ ∅ := by
  intro h
  have htrue : (true : Bool) ∈ boolDefault := by
    simp [boolDefault, Set.mem_singleton_iff]
  rw [h] at htrue
  simp at htrue

private theorem boolMeasure_default_ne_zero : boolMeasure boolDefault ≠ 0 := by
  rw [boolMeasure_default]
  have hpos : (0 : ℝ) < 1/4 := by norm_num
  have hlt : (0 : ENNReal) < ENNReal.ofReal (1/4 : ℝ) :=
    ENNReal.ofReal_pos.mpr hpos
  exact ne_of_gt hlt

private theorem boolMeasure_default_ne_top : boolMeasure boolDefault ≠ ⊤ := by
  rw [boolMeasure_default]
  exact ENNReal.ofReal_ne_top

private theorem boolIntegrableOn :
    IntegrableOn (fun ω : Bool => boolEAD ω * boolLGD ω) boolDefault
      boolMeasure := by
  have heq : (fun ω : Bool => boolEAD ω * boolLGD ω) =
      fun _ : Bool => (40 : ℝ) := by
    funext ω
    simp only [boolEAD, boolLGD]
    norm_num
  rw [heq]
  exact (MeasureTheory.integrable_const (40 : ℝ)).integrableOn

private theorem bool_pin_defaultProbability :
    defaultProbability boolMeasure boolDefault = (1/4 : ℝ) := by
  unfold defaultProbability MeasureTheory.Measure.real
  rw [boolMeasure_default, ENNReal.toReal_ofReal (by norm_num)]

private theorem bool_pin_conditionalExpectedLoss :
    conditionalExpectedLoss boolMeasure boolDefault boolEAD boolLGD =
      (40 : ℝ) := by
  unfold conditionalExpectedLoss
  have hcond : ProbabilityTheory.cond boolMeasure boolDefault =
      (boolMeasure boolDefault)⁻¹ • boolMeasure.restrict boolDefault := rfl
  have hrestrict : boolMeasure.restrict boolDefault =
      (boolMeasure boolDefault) • Measure.dirac (true : Bool) := by
    simp [boolDefault]
  have htoReal : (boolMeasure boolDefault).toReal = (1/4 : ℝ) := by
    rw [boolMeasure_default, ENNReal.toReal_ofReal (by norm_num)]
  rw [hcond, hrestrict, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
  simp only [smul_eq_mul, ENNReal.toReal_inv, htoReal]
  simp only [boolEAD, boolLGD]
  norm_num

private theorem bool_pin_expectedLoss :
    expectedLoss boolMeasure boolDefault boolEAD boolLGD = (10 : ℝ) := by
  unfold expectedLoss
  rw [MeasureTheory.integral_indicator boolDefault_measurable]
  have hrestrict : boolMeasure.restrict boolDefault =
      (boolMeasure boolDefault) • Measure.dirac (true : Bool) := by
    simp [boolDefault]
  have htoReal : (boolMeasure boolDefault).toReal = (1/4 : ℝ) := by
    rw [boolMeasure_default, ENNReal.toReal_ofReal (by norm_num)]
  rw [hrestrict, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_dirac]
  simp only [smul_eq_mul, htoReal]
  simp only [boolEAD, boolLGD]
  norm_num

private theorem bool_defaultProbability_bounds :
    0 < defaultProbability boolMeasure boolDefault ∧
      defaultProbability boolMeasure boolDefault < 1 := by
  rw [bool_pin_defaultProbability]
  constructor <;> norm_num

private theorem bool_cond_isProbabilityMeasure :
    IsProbabilityMeasure (ProbabilityTheory.cond boolMeasure boolDefault) :=
  ProbabilityTheory.cond_isProbabilityMeasure boolMeasure_default_ne_zero

private theorem bool_decomposition_check : (10 : ℝ) = (1/4 : ℝ) * 40 := by
  have hdecomp := expectedLoss_eq_defaultProbability_mul_conditionalExpectedLoss
    boolMeasure boolDefault_measurable boolMeasure_default_ne_zero
    boolIntegrableOn
  rw [bool_pin_expectedLoss, bool_pin_defaultProbability,
    bool_pin_conditionalExpectedLoss] at hdecomp
  exact hdecomp

end Examples

end MathlibExtTest.ExpectedLoss

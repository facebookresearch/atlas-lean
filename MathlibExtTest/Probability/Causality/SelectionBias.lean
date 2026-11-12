/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.SelectionBias
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic

/-! Example for `MathlibExt.Probability.Causality.SelectionBias`: four equally likely units,
treated set `{0, 1}`, `Y₀ = (1, 2, 0, 1)`, `Y₁ = (3, 3, 1, 1)`; the ATT is `3/2`, the selection
bias is `1`, and the observed difference in means is `5/2`. -/

@[expose] public section

namespace MathlibExtTest.Probability.Causality.SelectionBias

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality

open Matrix

noncomputable def testUniform : Measure (Fin 4) := (4 : ENNReal)⁻¹ • Measure.count

noncomputable def testTreated : Set (Fin 4) := {0, 1}

noncomputable def testY0 : Fin 4 → ℝ := ![1, 2, 0, 1]

noncomputable def testY1 : Fin 4 → ℝ := ![3, 3, 1, 1]

theorem testTreated_meas : MeasurableSet testTreated := by simp [testTreated]

theorem testToReal_zero : (0 : ENNReal).toReal = 0 := ENNReal.toReal_zero

theorem testToReal_one : (1 : ENNReal).toReal = 1 := ENNReal.toReal_one

theorem testToReal_four : (4 : ENNReal).toReal = 4 := by simp

theorem testToReal_two : (2 : ENNReal).toReal = 2 := by simp

theorem testTreated_coe : testTreated = ↑({0, 1} : Finset (Fin 4)) := by
  have hall : ∀ x : Fin 4,
      (x ∈ ({0, 1} : Set (Fin 4)) ↔ x ∈ ↑({0, 1} : Finset (Fin 4))) := by decide
  exact Set.ext hall

theorem testCompl_coe : testTreatedᶜ = ↑({2, 3} : Finset (Fin 4)) := by
  have hall : ∀ x : Fin 4,
      (x ∈ (({0, 1} : Set (Fin 4))ᶜ) ↔ x ∈ ↑({2, 3} : Finset (Fin 4))) := by decide
  exact Set.ext hall

theorem testCount_treated : Measure.count testTreated = 2 := by
  have hcard : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  simp only [testTreated_coe, MeasureTheory.Measure.count_apply_finset, hcard, Nat.cast_ofNat]

theorem testCount_compl : Measure.count testTreatedᶜ = 2 := by
  have hcard : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
  simp only [testCompl_coe, MeasureTheory.Measure.count_apply_finset, hcard, Nat.cast_ofNat]

theorem testMu_treated : testUniform testTreated = (4 : ENNReal)⁻¹ * 2 := by
  simp only [testUniform, MeasureTheory.Measure.smul_apply, smul_eq_mul, testCount_treated]

theorem testMu_compl : testUniform testTreatedᶜ = (4 : ENNReal)⁻¹ * 2 := by
  simp only [testUniform, MeasureTheory.Measure.smul_apply, smul_eq_mul, testCount_compl]

theorem testMu_treated_toReal : (testUniform testTreated).toReal = 1 / 2 := by
  simp only [testMu_treated, ENNReal.toReal_mul, ENNReal.toReal_inv, testToReal_four,
    testToReal_two]
  norm_num

theorem testMu_compl_toReal : (testUniform testTreatedᶜ).toReal = 1 / 2 := by
  simp only [testMu_compl, ENNReal.toReal_mul, ENNReal.toReal_inv, testToReal_four,
    testToReal_two]
  norm_num

theorem testMu_treated_ne_zero : testUniform testTreated ≠ 0 := by
  intro hcon
  have h2 := congrArg ENNReal.toReal hcon
  rw [testMu_treated_toReal, testToReal_zero] at h2
  norm_num at h2

theorem testMu_compl_ne_zero : testUniform testTreatedᶜ ≠ 0 := by
  intro hcon
  have h2 := congrArg ENNReal.toReal hcon
  rw [testMu_compl_toReal, testToReal_zero] at h2
  norm_num at h2

theorem testMu_treated_ne_top : testUniform testTreated ≠ ⊤ := by
  intro hcon
  have h2 := congrArg ENNReal.toReal hcon
  rw [testMu_treated_toReal, ENNReal.toReal_top] at h2
  norm_num at h2

theorem testMu_compl_ne_top : testUniform testTreatedᶜ ≠ ⊤ := by
  intro hcon
  have h2 := congrArg ENNReal.toReal hcon
  rw [testMu_compl_toReal, ENNReal.toReal_top] at h2
  norm_num at h2

theorem testCondT_prob : IsProbabilityMeasure testUniform[|testTreated] :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite testMu_treated_ne_zero
    testMu_treated_ne_top

theorem testCondTc_prob : IsProbabilityMeasure testUniform[|testTreatedᶜ] :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite testMu_compl_ne_zero
    testMu_compl_ne_top

example : att testUniform testTreated testY0 testY1 = 3 / 2
    ∧ selectionBias testUniform testTreated testY0 = 1
    ∧ diffInGroupMeans testUniform testTreated (observed testTreated testY0 testY1) = 5 / 2 := by
  have hTc : MeasurableSet testTreatedᶜ := testTreated_meas.compl
  haveI := testCondT_prob
  haveI := testCondTc_prob
  have n20 : (2 : Fin 4) ≠ 0 := by decide
  have n21 : (2 : Fin 4) ≠ 1 := by decide
  have n30 : (3 : Fin 4) ≠ 0 := by decide
  have n31 : (3 : Fin 4) ≠ 1 := by decide
  have m0 : (0 : Fin 4) ∈ testTreated := by simp [testTreated]
  have m1 : (1 : Fin 4) ∈ testTreated := by simp [testTreated]
  have m2 : (2 : Fin 4) ∉ testTreated := by simp [testTreated, n20, n21]
  have m3 : (3 : Fin 4) ∉ testTreated := by simp [testTreated, n30, n31]
  have y00 : testY0 0 = 1 := by rfl
  have y01 : testY0 1 = 2 := by rfl
  have y02 : testY0 2 = 0 := by rfl
  have y03 : testY0 3 = 1 := by rfl
  have y10 : testY1 0 = 3 := by rfl
  have y11 : testY1 1 = 3 := by rfl
  have y12 : testY1 2 = 1 := by rfl
  have y13 : testY1 3 = 1 := by rfl
  have hμ_single : ∀ x : Fin 4, (testUniform {x}).toReal = 1 / 4 := by
    intro x
    have h1 : testUniform {x} = (4 : ENNReal)⁻¹ * Measure.count {x} := by
      simp only [testUniform, MeasureTheory.Measure.smul_apply, smul_eq_mul]
    rw [h1, MeasureTheory.Measure.count_singleton, ENNReal.toReal_mul, ENNReal.toReal_inv,
      testToReal_four, testToReal_one]
    norm_num
  have iT0 : testTreated ∩ ({0} : Set (Fin 4)) = {0} := Set.inter_singleton_of_mem m0
  have iT1 : testTreated ∩ ({1} : Set (Fin 4)) = {1} := Set.inter_singleton_of_mem m1
  have iT2 : testTreated ∩ ({2} : Set (Fin 4)) = ∅ := Set.inter_singleton_eq_empty.mpr m2
  have iT3 : testTreated ∩ ({3} : Set (Fin 4)) = ∅ := Set.inter_singleton_eq_empty.mpr m3
  have iTc0 : testTreatedᶜ ∩ ({0} : Set (Fin 4)) = ∅ :=
    Set.inter_singleton_eq_empty.mpr (by simpa using m0)
  have iTc1 : testTreatedᶜ ∩ ({1} : Set (Fin 4)) = ∅ :=
    Set.inter_singleton_eq_empty.mpr (by simpa using m1)
  have iTc2 : testTreatedᶜ ∩ ({2} : Set (Fin 4)) = {2} :=
    Set.inter_singleton_of_mem (by simpa using m2)
  have iTc3 : testTreatedᶜ ∩ ({3} : Set (Fin 4)) = {3} :=
    Set.inter_singleton_of_mem (by simpa using m3)
  have cT0 : (testUniform[|testTreated]).real {0} = 1 / 2 := by
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.cond_apply testTreated_meas, iT0,
      ENNReal.toReal_mul, ENNReal.toReal_inv, testMu_treated_toReal, hμ_single 0]
    norm_num
  have cT1 : (testUniform[|testTreated]).real {1} = 1 / 2 := by
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.cond_apply testTreated_meas, iT1,
      ENNReal.toReal_mul, ENNReal.toReal_inv, testMu_treated_toReal, hμ_single 1]
    norm_num
  have cT2 : (testUniform[|testTreated]).real {2} = 0 := by
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.cond_apply testTreated_meas, iT2,
      MeasureTheory.measure_empty, mul_zero]
    exact testToReal_zero
  have cT3 : (testUniform[|testTreated]).real {3} = 0 := by
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.cond_apply testTreated_meas, iT3,
      MeasureTheory.measure_empty, mul_zero]
    exact testToReal_zero
  have cTc0 : (testUniform[|testTreatedᶜ]).real {0} = 0 := by
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.cond_apply hTc, iTc0,
      MeasureTheory.measure_empty, mul_zero]
    exact testToReal_zero
  have cTc1 : (testUniform[|testTreatedᶜ]).real {1} = 0 := by
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.cond_apply hTc, iTc1,
      MeasureTheory.measure_empty, mul_zero]
    exact testToReal_zero
  have cTc2 : (testUniform[|testTreatedᶜ]).real {2} = 1 / 2 := by
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.cond_apply hTc, iTc2,
      ENNReal.toReal_mul, ENNReal.toReal_inv, testMu_compl_toReal, hμ_single 2]
    norm_num
  have cTc3 : (testUniform[|testTreatedᶜ]).real {3} = 1 / 2 := by
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.cond_apply hTc, iTc3,
      ENNReal.toReal_mul, ENNReal.toReal_inv, testMu_compl_toReal, hμ_single 3]
    norm_num
  have oT0 : observed testTreated testY0 testY1 0 = 3 := by
    have h0c : (0 : Fin 4) ∉ testTreatedᶜ := by simpa using m0
    simp only [observed, Pi.add_apply, Set.indicator_of_mem m0 (f := testY1),
      Set.indicator_of_notMem h0c (f := testY0), add_zero, zero_add, y10]
  have oT1 : observed testTreated testY0 testY1 1 = 3 := by
    have h1c : (1 : Fin 4) ∉ testTreatedᶜ := by simpa using m1
    simp only [observed, Pi.add_apply, Set.indicator_of_mem m1 (f := testY1),
      Set.indicator_of_notMem h1c (f := testY0), add_zero, zero_add, y11]
  have oT2 : observed testTreated testY0 testY1 2 = 0 := by
    have h2c : (2 : Fin 4) ∈ testTreatedᶜ := by simpa using m2
    simp only [observed, Pi.add_apply, Set.indicator_of_notMem m2 (f := testY1),
      Set.indicator_of_mem h2c (f := testY0), add_zero, zero_add, y02]
  have oT3 : observed testTreated testY0 testY1 3 = 1 := by
    have h3c : (3 : Fin 4) ∈ testTreatedᶜ := by simpa using m3
    simp only [observed, Pi.add_apply, Set.indicator_of_notMem m3 (f := testY1),
      Set.indicator_of_mem h3c (f := testY0), add_zero, zero_add, y03]
  have intT_sub : ∫ ω, (testY1 ω - testY0 ω) ∂testUniform[|testTreated] = 3 / 2 := by
    have hInt : Integrable (fun ω => testY1 ω - testY0 ω) testUniform[|testTreated] :=
      MeasureTheory.Integrable.of_finite
    simp only [MeasureTheory.integral_fintype hInt, Fin.sum_univ_four, cT0, cT1, cT2, cT3,
      smul_eq_mul]
    norm_num [y00, y01, y02, y03, y10, y11, y12, y13]
  have intT_Y0 : ∫ ω, testY0 ω ∂testUniform[|testTreated] = 3 / 2 := by
    have hInt : Integrable (fun ω => testY0 ω) testUniform[|testTreated] :=
      MeasureTheory.Integrable.of_finite
    simp only [MeasureTheory.integral_fintype hInt, Fin.sum_univ_four, cT0, cT1, cT2, cT3,
      smul_eq_mul]
    norm_num [y00, y01, y02, y03]
  have intTc_Y0 : ∫ ω, testY0 ω ∂testUniform[|testTreatedᶜ] = 1 / 2 := by
    have hInt : Integrable (fun ω => testY0 ω) testUniform[|testTreatedᶜ] :=
      MeasureTheory.Integrable.of_finite
    simp only [MeasureTheory.integral_fintype hInt, Fin.sum_univ_four, cTc0, cTc1, cTc2, cTc3,
      smul_eq_mul]
    norm_num [y00, y01, y02, y03]
  have intT_obs :
      ∫ ω, observed testTreated testY0 testY1 ω ∂testUniform[|testTreated] = 3 := by
    have hInt : Integrable (fun ω => observed testTreated testY0 testY1 ω)
        testUniform[|testTreated] :=
      MeasureTheory.Integrable.of_finite
    simp only [MeasureTheory.integral_fintype hInt, Fin.sum_univ_four, cT0, cT1, cT2, cT3,
      smul_eq_mul]
    norm_num [oT0, oT1, oT2, oT3]
  have intTc_obs :
      ∫ ω, observed testTreated testY0 testY1 ω ∂testUniform[|testTreatedᶜ] = 1 / 2 := by
    have hInt : Integrable (fun ω => observed testTreated testY0 testY1 ω)
        testUniform[|testTreatedᶜ] :=
      MeasureTheory.Integrable.of_finite
    simp only [MeasureTheory.integral_fintype hInt, Fin.sum_univ_four, cTc0, cTc1, cTc2, cTc3,
      smul_eq_mul]
    norm_num [oT0, oT1, oT2, oT3]
  exact And.intro
    (by simp only [att]; exact intT_sub)
    (And.intro
      (by simp only [selectionBias, intT_Y0, intTc_Y0]; norm_num)
      (by simp only [diffInGroupMeans, intT_obs, intTc_obs]; norm_num))

end MathlibExtTest.Probability.Causality.SelectionBias

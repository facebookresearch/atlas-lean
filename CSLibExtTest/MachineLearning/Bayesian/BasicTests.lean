/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.Basic

@[expose] public section

/-!
# Tests for Bayes' rule for discrete observations
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Bayesian
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.Bayesian.Basic

/-- A test for a disease: `true` is a positive result. It has sensitivity `9/10` on the sick
(`true`) and false-positive rate `1/20` on the healthy (`false`). -/
noncomputable def test : Kernel Bool Bool :=
  Kernel.boolKernel
    ((1 / 20 : ℝ≥0) • Measure.dirac true + (19 / 20 : ℝ≥0) • Measure.dirac false)
    ((9 / 10 : ℝ≥0) • Measure.dirac true + (1 / 10 : ℝ≥0) • Measure.dirac false)

/-- One percent of the population is sick. -/
noncomputable def prevalence : Measure Bool :=
  (1 / 100 : ℝ≥0) • Measure.dirac true + (99 / 100 : ℝ≥0) • Measure.dirac false

instance : IsMarkovKernel test := by
  refine ⟨fun b ↦ ⟨?_⟩⟩
  cases b <;>
  · simp only [test, Kernel.boolKernel_apply, Bool.false_eq_true, ite_false, ite_true,
      Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul,
      mul_one, ← ENNReal.coe_add, ENNReal.coe_eq_one]
    apply NNReal.eq; push_cast; norm_num

instance : IsFiniteMeasure prevalence := by
  unfold prevalence; infer_instance

theorem test_true_true : test true {true} = ((9 / 10 : ℝ≥0) : ℝ≥0∞) := by
  simp [test, Kernel.boolKernel_apply]

theorem test_false_true : test false {true} = ((1 / 20 : ℝ≥0) : ℝ≥0∞) := by
  simp [test, Kernel.boolKernel_apply]

theorem prevalence_true : prevalence {true} = ((1 / 100 : ℝ≥0) : ℝ≥0∞) := by
  simp [prevalence]

theorem prevalence_false : prevalence {false} = ((99 / 100 : ℝ≥0) : ℝ≥0∞) := by
  simp [prevalence]

/-- A positive result has evidence `117/2000`. -/
theorem evidence_true : (test ∘ₘ prevalence) {true} = ((117 / 2000 : ℝ≥0) : ℝ≥0∞) := by
  rw [comp_apply_singleton_eq_tsum, tsum_bool, prevalence_true, prevalence_false,
    test_true_true, test_false_true, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add]
  norm_num

/-- **The base-rate effect**: after a positive test, the probability of being sick is only
`2/13`, about 15%. -/
theorem posterior_sick : (test†prevalence) true {true} = ((2 / 13 : ℝ≥0) : ℝ≥0∞) := by
  rw [posterior_apply_singleton test prevalence (by rw [evidence_true]; norm_num), tsum_bool,
    prevalence_true, prevalence_false, test_true_true, test_false_true, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, ← ENNReal.coe_add, ← ENNReal.coe_div (by norm_num)]
  norm_num

/-- After a positive test, "sick" is the maximum-likelihood hypothesis ... -/
theorem isMLE_sick : IsMLE test true true := by
  intro θ
  cases θ
  · rw [test_false_true, test_true_true, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast; norm_num
  · exact le_rfl

/-- ... but "healthy" is the MAP hypothesis: the prior outweighs the likelihood ratio. -/
theorem isMAP_healthy : IsMAP test prevalence true false := by
  rw [isMAP_iff test prevalence (by rw [evidence_true]; norm_num)]
  intro θ
  cases θ
  · exact le_rfl
  · rw [prevalence_true, prevalence_false, test_true_true, test_false_true, ← ENNReal.coe_mul,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast; norm_num

theorem not_isMAP_sick : ¬IsMAP test prevalence true true := by
  rw [isMAP_iff test prevalence (by rw [evidence_true]; norm_num)]
  intro h
  have := h false
  rw [prevalence_true, prevalence_false, test_true_true, test_false_true, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at this
  push_cast at this; norm_num at this

/-- Under a uniform prior, the MAP hypothesis is the maximum-likelihood one. -/
example : IsMAP test ((1 / 2 : ℝ≥0) • (Measure.dirac true + Measure.dirac false)) true true := by
  rw [isMAP_iff_isMLE_of_uniform test _ (c := ((1 / 2 : ℝ≥0) : ℝ≥0∞))
    (fun θ ↦ by cases θ <;> simp [ENNReal.smul_def]) (by simp)]
  · exact isMLE_sick
  · rw [comp_apply_singleton_eq_tsum, tsum_bool]
    simp [test_true_true, test_false_true, ENNReal.smul_def]

end CSLibExtTest.MachineLearning.Bayesian.Basic

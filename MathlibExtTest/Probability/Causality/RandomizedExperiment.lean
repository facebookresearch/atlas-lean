/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.RandomizedExperiment
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Tactic.NormNum

/-! Example for `MathlibExt.Probability.Causality.RandomizedExperiment`: a fair-coin treatment
independent of a fair-coin outcome type on `Bool × Bool`; the independence hypothesis holds
and the difference of the observed group means equals the ATE `3/2`. -/

@[expose] public section

namespace MathlibExtTest.Probability.Causality.RandomizedExperiment

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality

/-- Fair-coin marginal: uniform on `Bool`, via scaled counting measure (version-stable). -/
noncomputable def fairCoin : Measure Bool := (1 / 2 : ENNReal) • Measure.count

instance : IsProbabilityMeasure fairCoin where
  measure_univ := by
    rw [fairCoin, Measure.smul_apply, smul_eq_mul, Measure.count_univ,
      ENat.card_eq_coe_fintype_card, Fintype.card_bool]
    norm_num
    exact ENNReal.inv_mul_cancel (by simp) (by simp)

/-- Test treatment event: first coin is `true`. -/
noncomputable def testT : Set (Bool × Bool) := {ω | ω.1 = true}

/-- Test control potential outcome: second coin. -/
noncomputable def testY₀ : (Bool × Bool) → ℝ := fun ω => if ω.2 then 1 else 0

/-- Test treated potential outcome. -/
noncomputable def testY₁ : (Bool × Bool) → ℝ := fun ω => if ω.2 then 3 else 1

/-- Test law: product of two fair coins. -/
noncomputable def testμ : Measure (Bool × Bool) := fairCoin.prod fairCoin

instance : IsProbabilityMeasure testμ := by rw [testμ]; infer_instance

theorem testμ_T : testμ.real testT = 1 / 2 := by
  have hT : testT = {true} ×ˢ Set.univ := by
    rw [testT]
    ext ω
    simp
  rw [hT]
  show (fairCoin.prod fairCoin).real ({true} ×ˢ Set.univ) = 1 / 2
  rw [Measure.real_def, Measure.prod_prod]
  have h1 : fairCoin {true} = (1 / 2 : ENNReal) := by
    rw [fairCoin, Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
  have h2 : fairCoin Set.univ = 1 := measure_univ
  rw [h1, h2, mul_one, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]

theorem indepFun_test : IndepFun (testT.indicator (1 : (Bool × Bool) → ℝ))
    (fun ω => (testY₀ ω, testY₁ ω)) testμ := by
  have h := indepFun_prod (μ := fairCoin) (ν := fairCoin)
    (X := fun b : Bool => if b then (1 : ℝ) else 0)
    (Y := fun b : Bool => ((if b then (1 : ℝ) else 0), (if b then (3 : ℝ) else 1)))
    Measurable.of_discrete Measurable.of_discrete
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    (Filter.Eventually.of_forall fun ω => rfl)
  show (if ω.1 then (1 : ℝ) else 0) = testT.indicator 1 ω
  rw [testT]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases hω : ω.1 = true <;> simp [hω]

theorem integral_testATE : ∫ ω, (testY₁ ω - testY₀ ω) ∂testμ = 3 / 2 := by
  have hsing : ∀ ω : Bool × Bool, testμ.real {ω} = 1 / 4 := by
    intro ω
    have hset : ({ω} : Set (Bool × Bool)) = {ω.1} ×ˢ {ω.2} := by ext x; simp [Prod.ext_iff]
    rw [hset]
    show (fairCoin.prod fairCoin).real ({ω.1} ×ˢ {ω.2}) = 1 / 4
    rw [Measure.real_def, Measure.prod_prod]
    have h1 : ∀ b : Bool, fairCoin {b} = (1 / 2 : ENNReal) := by
      intro b
      rw [fairCoin, Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
    rw [h1, h1, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  rw [integral_fintype Integrable.of_finite]
  simp_rw [hsing]
  simp [Fintype.sum_prod_type, testY₀, testY₁, smul_eq_mul]
  norm_num

example : IndepFun (testT.indicator (1 : (Bool × Bool) → ℝ)) (fun ω => (testY₀ ω, testY₁ ω)) testμ ∧
    ∫ ω, observed testT testY₀ testY₁ ω ∂testμ[|testT] -
      ∫ ω, observed testT testY₀ testY₁ ω ∂testμ[|testTᶜ] = 3 / 2 := by
  refine ⟨indepFun_test, ?_⟩
  have hT : MeasurableSet testT := MeasurableSet.of_discrete
  have hpos : 0 < testμ.real testT := by rw [testμ_T]; norm_num
  have hlt : testμ.real testT < 1 := by rw [testμ_T]; norm_num
  have h : ∫ ω, observed testT testY₀ testY₁ ω ∂testμ[|testT] -
      ∫ ω, observed testT testY₀ testY₁ ω ∂testμ[|testTᶜ] =
      ∫ ω, (testY₁ ω - testY₀ ω) ∂testμ :=
    diff_integral_observed_cond_eq_ate_of_indepFun hT Measurable.of_discrete Measurable.of_discrete
      Integrable.of_finite Integrable.of_finite indepFun_test hpos hlt
  rw [h, integral_testATE]

end MathlibExtTest.Probability.Causality.RandomizedExperiment

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.ConditionalExpectationVariance
import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic

/-!
# Tests for the variance of a conditional expectation

Uniform `Fin 2` (as the Dirac mixture `(1/2) • δ_0 + (1/2) • δ_1`, avoiding the
deprecated `PMF.uniformOfFintype`) with the indicator payoff `Xtest`: the conditional
expectation given the trivial σ-algebra is the constant `1 / 2` (variance `0`), while
`Var[Xtest] = 1 / 4`, so the bound holds with left side `0` and right side `1 / 4`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.ConditionalExpectationVariance

open _root_.MathlibExt.Probability.Finance.ConditionalExpectationVariance
open MeasureTheory ProbabilityTheory
open ENNReal



/-- Uniform probability measure on `Fin 2` (weights `1 / 2, 1 / 2`). -/
noncomputable def μtest : Measure (Fin 2) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

instance : IsProbabilityMeasure μtest := by
  unfold μtest
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.indicator_of_mem, Set.mem_univ, Pi.one_apply, smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

/-- Indicator of the outcome `1`: `X 0 = 0`, `X 1 = 1`. -/
noncomputable def Xtest : Fin 2 → ℝ := fun i => (i.val : ℝ)

theorem test_memLp : MemLp Xtest 2 μtest := by
  apply MemLp.of_bound (Measurable.aestronglyMeasurable Measurable.of_discrete) 1
  filter_upwards with i
  unfold Xtest
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hi : i.val ≤ 1 := by omega
  exact_mod_cast hi

theorem integrable_Xtest_dirac (a : Fin 2) : Integrable Xtest (Measure.dirac a) :=
  integrable_dirac (by simp [Xtest])

theorem integrable_Xtest_smul (a : Fin 2) :
    Integrable Xtest ((1 / 2 : ℝ≥0∞) • Measure.dirac a) :=
  (integrable_Xtest_dirac a).smul_measure (by simp)

theorem integrable_Xtest_sq_dirac (a : Fin 2) :
    Integrable (Xtest ^ 2) (Measure.dirac a) :=
  integrable_dirac (by simp [Xtest, Pi.pow_apply])

theorem integrable_Xtest_sq_smul (a : Fin 2) :
    Integrable (Xtest ^ 2) ((1 / 2 : ℝ≥0∞) • Measure.dirac a) :=
  (integrable_Xtest_sq_dirac a).smul_measure (by simp)

theorem test_mean : μtest[Xtest] = 1 / 2 := by
  unfold μtest
  rw [integral_add_measure (integrable_Xtest_smul 0) (integrable_Xtest_smul 1),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  unfold Xtest
  simp

theorem test_second : μtest[Xtest ^ 2] = 1 / 2 := by
  unfold μtest
  rw [integral_add_measure (integrable_Xtest_sq_smul 0) (integrable_Xtest_sq_smul 1),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  unfold Xtest
  simp [Pi.pow_apply]

theorem test_variance : Var[Xtest; μtest] = 1 / 4 := by
  rw [ProbabilityTheory.variance_eq_sub test_memLp, test_mean, test_second]
  norm_num

theorem test_condExp : μtest[Xtest | ⊥] = fun _ => 1 / 2 := by
  rw [condExp_bot, test_mean]

theorem test_variance_const : Var[fun _ : Fin 2 => (1 / 2 : ℝ); μtest] = 0 := by
  rw [variance_eq_integral aemeasurable_const]
  simp

theorem test_variance_condExp : Var[μtest[Xtest | ⊥]; μtest] = 0 := by
  rw [test_condExp]
  exact test_variance_const

theorem test_bound : Var[μtest[Xtest | ⊥]; μtest] ≤ Var[Xtest; μtest] :=
  variance_condExp_le bot_le test_memLp

theorem test_bound_values :
    Var[μtest[Xtest | ⊥]; μtest] = 0 ∧ Var[Xtest; μtest] = 1 / 4 :=
  ⟨test_variance_condExp, test_variance⟩



end MathlibExtTest.Probability.Finance.ConditionalExpectationVariance

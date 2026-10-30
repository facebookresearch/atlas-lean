/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
public import MathlibExt.Probability.ProbabilityMassFunction.Expectation
import Mathlib.Tactic.NormNum

/-! # Tests of finite uniform samplers, event probabilities and expectations -/

open scoped ENNReal

universe u

example (b : Bool) : PMF.uniformFintype Bool b = (2 : ℝ≥0∞)⁻¹ := by
  simp

example (b : ULift.{u} Bool) :
    PMF.uniformFintype (ULift.{u} Bool) b = (2 : ℝ≥0∞)⁻¹ := by
  simp

example : (PMF.uniformFintype (Fin 4)).toOuterMeasure {0} = (4 : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_apply_singleton]
  simp

example : (PMF.uniformFintype (Fin 4)).toOuterMeasure {i | i = 0 ∨ i = 2} =
    (2 : ℝ≥0∞) / 4 := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype]
  calc
    _ = (4 : ℝ≥0∞)⁻¹ + (4 : ℝ≥0∞)⁻¹ := by
      norm_num [Set.indicator, PMF.uniformFintype_apply, Fin.sum_univ_four]
    _ = (2 : ℝ≥0∞) / 4 := by rw [div_eq_mul_inv, two_mul]

example : @PMF.toMeasure Bool ⊤ (PMF.uniformFintype Bool) {true} = (2 : ℝ≥0∞)⁻¹ := by
  letI : MeasurableSpace Bool := ⊤
  rw [PMF.toMeasure_uniformFintype_apply _ MeasurableSpace.measurableSet_top]
  have hcard : Fintype.card ({true} : Set Bool) = 1 := by
    rw [Fintype.card_of_subtype ({true} : Finset Bool) (by intro b; simp)]
    simp
  rw [hcard, Fintype.card_bool]
  simp

example : PMF.uniformFinset ({0, 1} : Finset ℕ) (by simp) 0 = (2 : ℝ≥0∞)⁻¹ := by
  simp

example : PMF.uniformFinset ({0, 1} : Finset ℕ) (by simp) 1 = (2 : ℝ≥0∞)⁻¹ := by
  simp

example : PMF.uniformFinset ({0, 1} : Finset ℕ) (by simp) 2 = 0 := by
  simp

example : (PMF.uniformFinset ({0, 1} : Finset ℕ) (by simp)).expect
    (fun n => (n : ℝ)) = 1 / 2 := by
  rw [PMF.expect_eq_sum_of_finite_support {0, 1} (by
    intro n hn
    rw [PMF.uniformFinset_apply]
    simp [hn])]
  norm_num [PMF.uniformFinset_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

example : (PMF.uniformFintype (Fin 3)).expect (fun i => (i.val : ℝ) ^ 2) = 5 / 3 := by
  rw [PMF.expect_uniformOfFintype]
  norm_num [Fin.sum_univ_three]

example : (PMF.uniformFintype (Fin 3)).expectENN (fun i => (i.val : ℝ≥0∞)) = 1 := by
  rw [PMF.expectENN_uniformOfFintype]
  have hthree : (3 : ℝ≥0∞)⁻¹ * 3 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  convert hthree using 1 <;> norm_num [Fin.sum_univ_three]

example : True := by
  fail_if_success
    solve
    | have : PMF (Fin 0) := PMF.uniformFintype (Fin 0)
      all_goals trivial
  trivial

/-- The counting probability of a singleton event, checked directly through
`PMF.toOuterMeasure_uniformFintype_apply`. -/
example : (PMF.uniformFintype (Fin 4)).toOuterMeasure {0} = (4 : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_uniformFintype_apply]
  simp [div_eq_mul_inv]

/-- Uniform on the full finset agrees with uniform on the finite type. -/
example :
    PMF.uniformFinset (Finset.univ : Finset (Fin 3)) Finset.univ_nonempty =
      PMF.uniformFintype (Fin 3) :=
  PMF.uniformFinset_univ

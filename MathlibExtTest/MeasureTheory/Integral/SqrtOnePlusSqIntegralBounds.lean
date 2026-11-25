/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Integral.SqrtOnePlusSqIntegralBounds
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open MathlibExt.MeasureTheory.SqrtOnePlusSqIntegralBoundsWanted
open scoped ENNReal NNReal

private noncomputable def twoAtoms : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)

private noncomputable def sample : ℝ → ℝ≥0 := ({1} : Set ℝ).indicator (fun _ => 2)

-- Equal masses at 0 and 1, with respective values 0 and 2, give mean 1.
example : Real.sqrt 2 ≤ (∫ x, Real.sqrt (1 + (sample x).toReal ^ 2) ∂twoAtoms) ∧
    (∫ x, Real.sqrt (1 + (sample x).toReal ^ 2) ∂twoAtoms) ≤ 2 := by
  let : IsProbabilityMeasure twoAtoms := ⟨by
    calc
      twoAtoms univ = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by simp [twoAtoms]
      _ = 1 := by rw [← two_mul, ENNReal.mul_inv_cancel (by simp) (by simp)]⟩
  have hmass : twoAtoms ({1} : Set ℝ) = (2 : ℝ≥0∞)⁻¹ := by norm_num [twoAtoms]
  have hsample : Measurable sample := measurable_const.indicator (measurableSet_singleton 1)
  have hmean : (∫⁻ x, sample x ∂twoAtoms) = 1 := by
    have he : (fun x => (sample x : ℝ≥0∞)) = ({1} : Set ℝ).indicator (fun _ => 2) := by
      funext x
      by_cases hx : x ∈ ({1} : Set ℝ) <;> simp [sample, hx]
    rw [he, lintegral_indicator (measurableSet_singleton 1), lintegral_const,
      Measure.restrict_apply_univ, hmass, ENNReal.mul_inv_cancel (by simp) (by simp)]
  have h := sqrt_one_add_sq_integral_le_and_le_one_add twoAtoms sample hsample
    (by rw [hmean]; simp) 1 (by rw [hmean, ENNReal.toReal_one])
  simpa only [one_pow, one_add_one_eq_two] using h

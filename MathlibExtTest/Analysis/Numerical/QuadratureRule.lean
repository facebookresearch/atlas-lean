/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.Analysis.Numerical.QuadratureRule

open MeasureTheory MetaMathlibExt Set
open scoped Interval

namespace MathlibExtTest.Analysis.Numerical.QuadratureRule

noncomputable section

private theorem unitInterval_pow (k : ℕ) :
    (∫ x : Ioo (0 : ℝ) 1, (x : ℝ) ^ k ∂(Measure.comap Subtype.val (volume : Measure ℝ))) =
      1 / ((k : ℝ) + 1) := by
  rw [integral_subtype_comap measurableSet_Ioo (fun x : ℝ ↦ x ^ k),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_pow]
  simp [zero_pow (Nat.succ_ne_zero k)]

private theorem unitInterval_const :
    (∫ _ : Ioo (0 : ℝ) 1, (1 : ℝ) ∂(Measure.comap Subtype.val (volume : Measure ℝ))) = 1 := by
  simpa using unitInterval_pow 0

private theorem unitInterval_id :
    (∫ x : Ioo (0 : ℝ) 1, (x : ℝ) ∂(Measure.comap Subtype.val (volume : Measure ℝ))) = 1 / 2 := by
  simpa only [pow_one, Nat.cast_one, one_add_one_eq_two] using unitInterval_pow 1

private def trapezoid : QuadratureRule 0 1 2 where
  lt := zero_lt_one
  node i := if i = 0 then 0 else 1
  node_mem i := by split <;> norm_num [mem_Icc]
  coeff _ := 1 / 2
  weight _ := 1
  continuous_weight := continuous_const
  weight_nonneg _ := zero_le_one
  integrable_weight := .of_integral_ne_zero (by rw [unitInterval_const]; exact one_ne_zero)
  weight_mass_pos := by rw [unitInterval_const]; exact one_pos

private theorem trapezoid_moment (k : ℕ) :
    trapezoid.weightedIntegral (fun x ↦ x ^ k) = 1 / ((k : ℝ) + 1) := by
  simpa only [QuadratureRule.weightedIntegral, trapezoid, mul_one] using unitInterval_pow k

/-- The unweighted trapezoid rule on `[0, 1]` is exact on affine polynomials. -/
private theorem trapezoid_exactUpTo_one : trapezoid.ExactUpTo 1 := by
  refine trapezoid.exactUpTo_iff_moments.mpr fun k hk ↦ ?_
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl <;> rw [trapezoid_moment] <;>
    norm_num [QuadratureRule.eval, trapezoid, Fin.sum_univ_two]

/-- The trapezoid rule gives `1/2` for `x²`, not its integral `1/3`. -/
private theorem trapezoid_not_exactUpTo_two : ¬trapezoid.ExactUpTo 2 := by
  intro h
  have hm := trapezoid.exactUpTo_iff_moments.mp h 2 le_rfl
  rw [trapezoid_moment] at hm
  norm_num [QuadratureRule.eval, trapezoid, Fin.sum_univ_two] at hm

private def centroid : QuadratureRule 0 1 1 where
  lt := zero_lt_one
  node _ := 2 / 3
  node_mem _ := by norm_num [mem_Icc]
  coeff _ := 1 / 2
  weight x := x
  continuous_weight := continuous_subtype_val
  weight_nonneg x := x.property.1.le
  integrable_weight := .of_integral_ne_zero (by rw [unitInterval_id]; norm_num)
  weight_mass_pos := by rw [unitInterval_id]; norm_num

private theorem centroid_moment (k : ℕ) :
    centroid.weightedIntegral (fun x ↦ x ^ k) = 1 / ((k : ℝ) + 2) := by
  simpa only [QuadratureRule.weightedIntegral, centroid, pow_succ, Nat.cast_succ,
    add_assoc, one_add_one_eq_two] using unitInterval_pow (k + 1)

/-- For the nonconstant weight `w(x) = x`, the node `2/3` with coefficient `1/2`
reproduces both the mass and the first moment. -/
private theorem centroid_exactUpTo_one : centroid.ExactUpTo 1 := by
  refine centroid.exactUpTo_iff_moments.mpr fun k hk ↦ ?_
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl <;> rw [centroid_moment] <;>
    norm_num [QuadratureRule.eval, centroid, Fin.sum_univ_one]

private def rightEndpoint (x : ℝ) : ℝ := if x = 1 then 1 else 0

/-- The right endpoint contributes to quadrature but not to the integral. The product is integrable
on the open interval even though the integrand is discontinuous at the endpoint. -/
private theorem rightEndpoint_values :
    Integrable (fun x : Ioo (0 : ℝ) 1 ↦ rightEndpoint x * trapezoid.weight x)
        (Measure.comap Subtype.val (volume : Measure ℝ)) ∧
      trapezoid.eval rightEndpoint = 1 / 2 ∧ trapezoid.weightedIntegral rightEndpoint = 0 := by
  have h : ∀ x : Ioo (0 : ℝ) 1, rightEndpoint x * trapezoid.weight x = 0 := fun x ↦ by
    simp [rightEndpoint, ne_of_lt x.property.2]
  refine ⟨?_, ?_, ?_⟩
  · simp only [h]
    exact integrable_zero _ ℝ _
  · norm_num [QuadratureRule.eval, trapezoid, Fin.sum_univ_two, rightEndpoint]
  · simp only [QuadratureRule.weightedIntegral, h, integral_zero]

end
end MathlibExtTest.Analysis.Numerical.QuadratureRule

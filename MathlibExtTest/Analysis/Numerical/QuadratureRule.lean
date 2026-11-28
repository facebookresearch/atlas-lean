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

private theorem unitInterval_integral (f : ℝ → ℝ) :
    (∫ x : Ioo (0 : ℝ) 1, f x ∂(Measure.comap Subtype.val (volume : Measure ℝ))) =
      ∫ x in (0 : ℝ)..1, f x := by
  rw [integral_subtype_comap measurableSet_Ioo f, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

private theorem unitInterval_pow (k : ℕ) :
    (∫ x : Ioo (0 : ℝ) 1, (x : ℝ) ^ k ∂(Measure.comap Subtype.val (volume : Measure ℝ))) =
      1 / ((k : ℝ) + 1) := by
  rw [unitInterval_integral (fun x : ℝ ↦ x ^ k), integral_pow]
  simp [zero_pow (Nat.succ_ne_zero k)]

private def unitWeight : QuadratureWeight 0 1 := QuadratureWeight.one zero_lt_one

private def trapezoid : QuadratureRule 0 1 2 where
  node i := if i = 0 then 0 else 1
  node_mem i := by split <;> norm_num [mem_Icc]
  coeff _ := 1 / 2

private theorem trapezoid_moment (k : ℕ) :
    unitWeight.weightedIntegral (fun x ↦ x ^ k) = 1 / ((k : ℝ) + 1) := by
  simpa only [QuadratureWeight.weightedIntegral, unitWeight, QuadratureWeight.one, mul_one]
    using unitInterval_pow k

/-- The unweighted trapezoid rule on `[0, 1]` is exact on affine polynomials. -/
private theorem trapezoid_exactUpTo_one : trapezoid.ExactUpTo unitWeight 1 := by
  refine (trapezoid.exactUpTo_iff_moments unitWeight).mpr fun k hk ↦ ?_
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl <;> rw [trapezoid_moment] <;>
    norm_num [QuadratureRule.eval, trapezoid, Fin.sum_univ_two]

/-- The trapezoid rule gives `1/2` for `x²`, not its integral `1/3`. -/
private theorem trapezoid_not_exactUpTo_two : ¬trapezoid.ExactUpTo unitWeight 2 := by
  intro h
  have hm := (trapezoid.exactUpTo_iff_moments unitWeight).mp h 2 le_rfl
  rw [trapezoid_moment] at hm
  norm_num [QuadratureRule.eval, trapezoid, Fin.sum_univ_two] at hm

private def linearWeight : QuadratureWeight 0 1 where
  lt := zero_lt_one
  weight x := x
  continuous_weight := continuous_subtype_val
  weight_nonneg x := x.property.1.le
  weight_mass_pos := by
    have h := unitInterval_pow 1
    simp only [pow_one, Nat.cast_one, one_add_one_eq_two] at h
    rw [h]
    norm_num

private def centroid : QuadratureRule 0 1 1 where
  node _ := 2 / 3
  node_mem _ := by norm_num [mem_Icc]
  coeff _ := 1 / 2

private theorem centroid_moment (k : ℕ) :
    linearWeight.weightedIntegral (fun x ↦ x ^ k) = 1 / ((k : ℝ) + 2) := by
  simpa only [QuadratureWeight.weightedIntegral, linearWeight, pow_succ, Nat.cast_succ,
    add_assoc, one_add_one_eq_two] using unitInterval_pow (k + 1)

/-- For the nonconstant weight `w(x) = x`, the node `2/3` with coefficient `1/2`
reproduces both the mass and the first moment. -/
private theorem centroid_exactUpTo_one : centroid.ExactUpTo linearWeight 1 := by
  refine (centroid.exactUpTo_iff_moments linearWeight).mpr fun k hk ↦ ?_
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl <;> rw [centroid_moment] <;>
    norm_num [QuadratureRule.eval, centroid, Fin.sum_univ_one]

private def rightEndpoint (x : ℝ) : ℝ := if x = 1 then 1 else 0

/-- The right endpoint contributes to quadrature but not to the integral. The product is integrable
on the open interval even though the integrand is discontinuous at the endpoint. -/
private theorem rightEndpoint_values :
    Integrable (fun x : Ioo (0 : ℝ) 1 ↦ rightEndpoint x * unitWeight.weight x)
        (Measure.comap Subtype.val (volume : Measure ℝ)) ∧
      trapezoid.eval rightEndpoint = 1 / 2 ∧ unitWeight.weightedIntegral rightEndpoint = 0 := by
  have h : ∀ x : Ioo (0 : ℝ) 1, rightEndpoint x * unitWeight.weight x = 0 := fun x ↦ by
    simp [rightEndpoint, ne_of_lt x.property.2]
  refine ⟨?_, ?_, ?_⟩
  · simp only [h]
    exact integrable_zero _ ℝ _
  · norm_num [QuadratureRule.eval, trapezoid, Fin.sum_univ_two, rightEndpoint]
  · simp only [QuadratureWeight.weightedIntegral, h, integral_zero]

private theorem unitInterval_rpow {r : ℝ} (hr : -1 < r) :
    (∫ x : Ioo (0 : ℝ) 1, (x : ℝ) ^ r ∂(Measure.comap Subtype.val (volume : Measure ℝ))) =
      1 / (r + 1) := by
  have hpos : 0 < r + 1 := by
    simpa only [add_neg_cancel, add_comm 1 r] using add_lt_add_right hr 1
  rw [unitInterval_integral (fun x : ℝ ↦ x ^ r), integral_rpow (Or.inl hr)]
  simp [Real.zero_rpow hpos.ne']

private theorem unitInterval_neg_half :
    (∫ x : Ioo (0 : ℝ) 1, (x : ℝ) ^ (-(1 / 2 : ℝ))
      ∂(Measure.comap Subtype.val (volume : Measure ℝ))) = 2 := by
  rw [unitInterval_rpow (by norm_num)]
  norm_num

private def invSqrtWeight : QuadratureWeight 0 1 where
  lt := zero_lt_one
  weight x := (x : ℝ) ^ (-(1 / 2 : ℝ))
  continuous_weight := continuous_subtype_val.rpow_const fun x ↦ Or.inl x.property.1.ne'
  weight_nonneg x := (Real.rpow_pos_of_pos x.property.1 _).le
  weight_mass_pos := by rw [unitInterval_neg_half]; norm_num

/-- Every right neighborhood of zero contains points where the weight exceeds any given bound. -/
private theorem invSqrtWeight_unbounded_near_zero (M ε : ℝ) (hε : 0 < ε) :
    ∃ x : Ioo (0 : ℝ) 1, (x : ℝ) < ε ∧ M < invSqrtWeight.weight x := by
  let t : ℝ := max M 0 + 1
  have ht : 0 < t := add_pos_of_nonneg_of_pos (le_max_right M 0) zero_lt_one
  have hMt : M < t := (le_max_left M 0).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  let x₀ : ℝ := t ^ (-2 : ℝ)
  let x : ℝ := min x₀ (min (ε / 2) (1 / 2))
  have hx : 0 < x := lt_min (Real.rpow_pos_of_pos ht _) (lt_min (half_pos hε) (by norm_num))
  have hxe : x < ε := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hε)
  have hx1 : x < 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  refine ⟨⟨x, hx, hx1⟩, hxe, ?_⟩
  change M < x ^ (-(1 / 2 : ℝ))
  have hle : x₀ ^ (-(1 / 2 : ℝ)) ≤ x ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx (min_le_left _ _) (by norm_num)
  have heq : x₀ ^ (-(1 / 2 : ℝ)) = t := by
    dsimp only [x₀]
    rw [← Real.rpow_mul ht.le, show (-2 : ℝ) * -(1 / 2) = 1 by norm_num, Real.rpow_one]
  rw [heq] at hle
  exact hMt.trans_le hle

private theorem invSqrtWeight_integrable_x :
    Integrable (fun x : Ioo (0 : ℝ) 1 ↦ (x : ℝ) * invSqrtWeight.weight x)
      (Measure.comap Subtype.val (volume : Measure ℝ)) :=
  invSqrtWeight.integrable_mul_weight_of_continuousOn continuous_id.continuousOn

private theorem invSqrtWeight_mass : invSqrtWeight.weightedIntegral (fun _ ↦ 1) = 2 := by
  simpa only [QuadratureWeight.weightedIntegral, invSqrtWeight, one_mul] using unitInterval_neg_half

private theorem invSqrtWeight_first_moment : invSqrtWeight.weightedIntegral id = 2 / 3 := by
  have h (x : Ioo (0 : ℝ) 1) : (x : ℝ) * invSqrtWeight.weight x = (x : ℝ) ^ (1 / 2 : ℝ) := by
    change (x : ℝ) * (x : ℝ) ^ (-(1 / 2 : ℝ)) = (x : ℝ) ^ (1 / 2 : ℝ)
    calc
      _ = (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add x.property.1, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num]
  simp only [QuadratureWeight.weightedIntegral, id_eq, h]
  rw [unitInterval_rpow (by norm_num)]
  norm_num

private def invSqrtCentroid : QuadratureRule 0 1 1 where
  node _ := 1 / 3
  node_mem _ := by norm_num [mem_Icc]
  coeff _ := 2

/-- The weight `x ^ (-1/2)` has mass `2` and first moment `2/3`, giving exactness
through degree one for the node `1/3` with coefficient `2`. -/
private theorem invSqrtCentroid_exactUpTo_one : invSqrtCentroid.ExactUpTo invSqrtWeight 1 := by
  refine (invSqrtCentroid.exactUpTo_iff_moments invSqrtWeight).mpr fun k hk ↦ ?_
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl
  · simp only [pow_zero, invSqrtWeight_mass]
    norm_num [QuadratureRule.eval, invSqrtCentroid, Fin.sum_univ_one]
  · simp only [pow_one]
    change invSqrtCentroid.eval id = invSqrtWeight.weightedIntegral id
    rw [invSqrtWeight_first_moment]
    norm_num [QuadratureRule.eval, invSqrtCentroid, Fin.sum_univ_one, id_eq]

end
end MathlibExtTest.Analysis.Numerical.QuadratureRule

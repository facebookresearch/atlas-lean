/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexLiteralHWAugment
import Code.Universality.HexContentHalfBound

namespace StatMech.Universality

open scoped BigOperators

noncomputable section




theorem hlhp_finite_partial_bound
    (a : ℂ) (h0 : ℤ) (N : ℕ) {x : ℝ} (hx : 0 < x)
    (ups : ℕ → ℝ) (hups : ∀ T, 0 ≤ ups T)
    (hmul : Multipliable (fun T => 1 + ups T))
    (hlower : ∀ T,
      hchb_bridgeMass
          (hlha_augmentedTwoHalfData a h0 N).lowerImage x T ≤ ups T)
    (hupper : ∀ T,
      hchb_bridgeMass
          (hlha_augmentedTwoHalfData a h0 N).upperImage x T ≤ ups T) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ 2)⁻¹ * (∏' T, (1 + ups T)) ^ 2 := by
  let H := hlha_augmentedTwoHalfData a h0 N
  let P : ℝ := ∏' T, (1 + ups T)
  have hlo :
      (∑ s ∈ H.lowerImage, hhc_halfWeight x s) ≤ P := by
    exact hchb_sum_halfWeight_le_tprod H.lowerImage (le_of_lt hx)
      ups hups hmul hlower
  have hup :
      (∑ s ∈ H.upperImage, hhc_halfWeight x s) ≤ P := by
    exact hchb_sum_halfWeight_le_tprod H.upperImage (le_of_lt hx)
      ups hups hmul hupper
  have hupper_nn : 0 ≤ ∑ s ∈ H.upperImage, hhc_halfWeight x s := by
    exact Finset.sum_nonneg fun s _ => hhc_halfWeight_nonneg (le_of_lt hx) s
  have hP_one : 1 ≤ P := by
    have h := hexSeams_prod_one_add_le_tprod ups hups hmul 0
    simpa [P] using h
  calc
    (∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n) ≤
        (x ^ 2)⁻¹ *
          ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
            (∑ s ∈ H.upperImage, hhc_halfWeight x s)) :=
      hlha_finite_partial_bound a h0 N hx
    _ ≤ (x ^ 2)⁻¹ * (P * P) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul hlo hup hupper_nn (le_trans (by norm_num) hP_one)
      · positivity
    _ = (x ^ 2)⁻¹ * P ^ 2 := by ring



theorem hlhp_summable_of_content_masses
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (ups : ℕ → ℝ) (hups : ∀ T, 0 ≤ ups T)
    (hsum : Summable ups)
    (hlower : ∀ N T,
      hchb_bridgeMass
          (hlha_augmentedTwoHalfData a h0 N).lowerImage x T ≤ ups T)
    (hupper : ∀ N T,
      hchb_bridgeMass
          (hlha_augmentedTwoHalfData a h0 N).upperImage x T ≤ ups T) :
    Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
  have hmul : Multipliable (fun T => 1 + ups T) :=
    hex_bridge_multipliable ups hsum
  apply summable_of_sum_range_le
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hx) _)
  · intro N
    simpa [hlc_sawCountR] using
      hlhp_finite_partial_bound a h0 N hx ups hups hmul
        (hlower N) (hupper N)

end

end StatMech.Universality

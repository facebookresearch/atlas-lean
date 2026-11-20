/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib

namespace StatMech.Universality

open scoped BigOperators

noncomputable section



theorem finiteTagged_sum_le_card_mul_tsum
    {B Tag W : Type*} [Fintype Tag]
    (S : Finset B) (encode : B → Tag × W)
    (hinj : Set.InjOn encode (S : Set B))
    (rawWeight : B → ℝ) (columnWeight : W → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hcolnn : ∀ w, 0 ≤ columnWeight w)
    (hcolsum : Summable columnWeight)
    (hweight : ∀ b ∈ S,
      rawWeight b ≤ K * columnWeight (encode b).2) :
    ∑ b ∈ S, rawWeight b ≤
      K * Fintype.card Tag * ∑' w, columnWeight w := by
  classical
  let productWeight : Tag × W → ℝ := fun p => columnWeight p.2
  have hproduct_nn : ∀ p, 0 ≤ productWeight p := fun p => hcolnn p.2
  have hproduct_sum : Summable productWeight := by
    rw [summable_prod_of_nonneg hproduct_nn]
    refine ⟨fun _ => hcolsum, ?_⟩
    exact Summable.of_finite
  have hfinite :
      ∑ b ∈ S, columnWeight (encode b).2 ≤
        ∑' p : Tag × W, productWeight p := by
    change (∑ b ∈ S, productWeight (encode b)) ≤
      ∑' p : Tag × W, productWeight p
    rw [← Finset.sum_image hinj]
    exact hproduct_sum.sum_le_tsum (S.image encode)
      (fun p _ => hproduct_nn p)
  have hproduct_tsum :
      (∑' p : Tag × W, productWeight p) =
        Fintype.card Tag * ∑' w, columnWeight w := by
    rw [hproduct_sum.tsum_prod, tsum_fintype]
    simp [productWeight, nsmul_eq_mul]
  calc
    ∑ b ∈ S, rawWeight b ≤
        ∑ b ∈ S, K * columnWeight (encode b).2 := by
      exact Finset.sum_le_sum fun b hb => hweight b hb
    _ = K * ∑ b ∈ S, columnWeight (encode b).2 := by
      rw [Finset.mul_sum]
    _ ≤ K * ∑' p : Tag × W, productWeight p :=
      mul_le_mul_of_nonneg_left hfinite hK
    _ = K * Fintype.card Tag * ∑' w, columnWeight w := by
      rw [hproduct_tsum]
      ring




theorem raw_pow_le_inv_mul_endpoint_pow
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1)
    (rawLen endpointLen : ℕ)
    (hlen : endpointLen = rawLen ∨ endpointLen = rawLen + 1) :
    x ^ rawLen ≤ x⁻¹ * x ^ endpointLen := by
  rcases hlen with hlen | hlen
  · rw [hlen]
    calc
      x ^ rawLen = 1 * x ^ rawLen := by ring
      _ ≤ x⁻¹ * x ^ rawLen :=
        mul_le_mul_of_nonneg_right ((one_le_inv₀ hx).2 hxone)
          (pow_nonneg (le_of_lt hx) _)
  · rw [hlen, pow_succ]
    have hcancel : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx)
    calc
      x ^ rawLen = 1 * x ^ rawLen := by ring
      _ = (x⁻¹ * x) * x ^ rawLen := by rw [hcancel]
      _ = x⁻¹ * (x ^ rawLen * x) := by ring
      _ ≤ x⁻¹ * (x ^ rawLen * x) := le_rfl

end

end StatMech.Universality

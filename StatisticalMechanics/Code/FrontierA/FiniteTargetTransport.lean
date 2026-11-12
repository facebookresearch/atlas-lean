/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib

open Set
open scoped ENNReal

namespace StatMech.FrontierA

variable {alpha : Type*}


noncomputable def finiteTargetTransport (C : Set alpha) (N : Finset alpha)
    (x y : alpha) : ℝ≥0∞ := by
  classical
  exact if x ∈ C ∧ y ∈ N then ((N.card : ℝ≥0∞)⁻¹) else 0


theorem finiteTargetTransport_outside (C : Set alpha) (N : Finset alpha)
    {x : alpha} (hx : x ∉ C) (y : alpha) :
    finiteTargetTransport C N x y = 0 := by
  simp [finiteTargetTransport, hx]


theorem finiteTargetTransport_outgoing_eq_one
    (C : Set alpha) (N : Finset alpha) (hN : N.Nonempty)
    {x : alpha} (hx : x ∈ C) :
    ∑' y : alpha, finiteTargetTransport C N x y = 1 := by
  classical
  rw [tsum_eq_sum (s := N)]
  · calc
      (∑ y ∈ N, finiteTargetTransport C N x y) =
          ∑ _y ∈ N, ((N.card : ℝ≥0∞)⁻¹) := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [finiteTargetTransport, hx, hy]
      _ = (N.card : ℝ≥0∞) * (N.card : ℝ≥0∞)⁻¹ := by
        simp [nsmul_eq_mul]
      _ = 1 := by
        have hcard : (N.card : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast N.card_ne_zero.mpr hN
        exact ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top N.card)
  · intro y hy
    simp [finiteTargetTransport, hy]



theorem finiteTargetTransport_outgoing_le_one
    (C : Set alpha) (N : Finset alpha) (x : alpha) :
    ∑' y : alpha, finiteTargetTransport C N x y ≤ 1 := by
  classical
  by_cases hN : N.Nonempty
  · by_cases hx : x ∈ C
    · rw [finiteTargetTransport_outgoing_eq_one C N hN hx]
    · simp [finiteTargetTransport, hx]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hN]
    simp [finiteTargetTransport]



theorem finiteTargetTransport_incoming_eq_top
    (C : Set alpha) (N : Finset alpha) (hC : C.Infinite)
    (_hN : N.Nonempty) {y : alpha} (hy : y ∈ N) :
    ∑' x : alpha, finiteTargetTransport C N x y = ⊤ := by
  classical
  let c : ℝ≥0∞ := (N.card : ℝ≥0∞)⁻¹
  have hc : c ≠ 0 := by
    apply ENNReal.inv_ne_zero.mpr
    exact ENNReal.natCast_ne_top N.card
  calc
    (∑' x : alpha, finiteTargetTransport C N x y) =
        ∑' x : C, c := by
      have hfun : (fun x : alpha => finiteTargetTransport C N x y) =
          C.indicator (fun _ => c) := by
        funext x
        by_cases hx : x ∈ C
        · simp [finiteTargetTransport, c, hx, hy]
        · simp [finiteTargetTransport, c, hx]
      rw [hfun, ← tsum_subtype C (fun _ : alpha => c)]
    _ = C.encard * c := ENNReal.tsum_set_const C c
    _ = ⊤ := by
      rw [Set.encard_eq_top hC]
      exact ENNReal.top_mul hc



theorem finiteTargetTransport_image {beta : Type*} [DecidableEq beta]
    (f : alpha → beta) (hf : Function.Injective f)
    (C : Set alpha) (N : Finset alpha) (x y : alpha) :
    finiteTargetTransport (f '' C) (N.image f) (f x) (f y) =
      finiteTargetTransport C N x y := by
  classical
  have hxmem : f x ∈ f '' C ↔ x ∈ C := by
    constructor
    · rintro ⟨z, hz, hzx⟩
      simpa [hf hzx] using hz
    · exact fun hx => ⟨x, hx, rfl⟩
  have hymem : f y ∈ N.image f ↔ y ∈ N := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, hzy⟩
      simpa [hf hzy] using hz
    · exact fun hy => ⟨y, hy, rfl⟩
  have hcard : (N.image f).card = N.card :=
    Finset.card_image_of_injective N hf
  unfold finiteTargetTransport
  rw [hcard]
  simp only [hxmem, hymem]

end StatMech.FrontierA

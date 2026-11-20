/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWEdgeScale









namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_loopWeight_scaleColumns_zero
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (S : Finset E) (Lambda : Matrix E E ℂ) (d : Fin n → E) :
    ons_loopWeight (ons_scaleColumns S 0 Lambda) d =
      if ∃ k, d k ∈ S then 0 else ons_loopWeight Lambda d := by
  by_cases hhit : ∃ k, d k ∈ S
  · rw [if_pos hhit]
    obtain ⟨j, hj⟩ := hhit
    unfold ons_loopWeight
    apply Finset.prod_eq_zero (Finset.mem_univ (j - 1))
    simp only [ons_scaleColumns]
    have hidx : (j - 1 + 1 : Fin n) = j := by
      abel
    rw [hidx, if_pos hj, zero_mul]
  · rw [if_neg hhit]
    unfold ons_loopWeight
    apply Finset.prod_congr rfl
    intro k hk
    simp only [ons_scaleColumns]
    rw [if_neg (fun h => hhit ⟨k + 1, h⟩)]

theorem ons_detWalkRoot_scaleColumns_zero_eq_mask
    {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (Lambda : Matrix E E ℂ) :
    ons_detWalkRoot (ons_scaleColumns S 0 Lambda) =
      ons_detWalkRoot (ons_maskMatrix S Lambda) := by
  unfold ons_detWalkRoot
  apply congrArg Complex.exp
  congr 1
  apply congrArg Neg.neg
  apply tsum_congr
  intro n
  apply congrArg (· / ((n : ℂ) + 1))
  apply Finset.sum_congr rfl
  intro d hd
  rw [show (∏ k : Fin (n + 1),
        ons_scaleColumns S 0 Lambda (d k) (d (k + 1))) =
      ons_loopWeight (ons_scaleColumns S 0 Lambda) d from rfl,
    ons_loopWeight_scaleColumns_zero,
    show (∏ k : Fin (n + 1),
        ons_maskMatrix S Lambda (d k) (d (k + 1))) =
      ons_loopWeight (ons_maskMatrix S Lambda) d from rfl,
    ons_loopWeight_maskMatrix]

theorem ons_detWalkRoot_zeroEdge_eq_mask
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega u v : ℂ) (e : ons_Dart L) :
    ons_detWalkRoot
        (ons_KWmatWeightedPhase L
          (ons_scaleEdgeWeight weight (ons_portEdge L e) 0) omega u v) =
      ons_detWalkRoot
        (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L))
          (ons_KWmatWeightedPhase L weight omega u v)) := by
  rw [ons_KWmatWeightedPhase_scaleEdge]
  exact ons_detWalkRoot_scaleColumns_zero_eq_mask _ _

end StatMech.Onsager

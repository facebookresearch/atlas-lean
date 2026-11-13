/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWMultiaffine
import Code.Onsager.KWWeightedBounds









namespace StatMech.Onsager

open Matrix BigOperators

theorem norm_ons_scaleEdgeWeight_le
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (edge : Sym2 (ZMod L × ZMod L)) (t : ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hweight : ∀ f, ‖weight f‖ ≤ q) (ht : ‖t‖ ≤ 1)
    (f : Sym2 (ZMod L × ZMod L)) :
    ‖ons_scaleEdgeWeight weight edge t f‖ ≤ q := by
  unfold ons_scaleEdgeWeight
  split
  · rw [norm_mul]
    calc
      ‖t‖ * ‖weight f‖ = ‖weight f‖ * ‖t‖ := mul_comm _ _
      _ ≤ q * 1 := mul_le_mul (hweight f) ht (norm_nonneg _) hq
      _ = q := mul_one q
  · exact hweight f

theorem ons_detWalkRoot_scaleEdge_affine_of_bound
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (q : ℝ) (hq : 0 ≤ q)
    (hweight : ∀ edge, ‖weight edge‖ ≤ q)
    (t : ℂ) (ht : ‖t‖ ≤ 1) (e : ons_Dart L)
    (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹) :
    ons_detWalkRoot
        (ons_KWmatWeightedPhase L
          (ons_scaleEdgeWeight weight (ons_portEdge L e) t) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
          (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L))
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_KWmatWeightedPhase L weight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))
          e (ons_dartRev L e) s) := by
  apply ons_detWalkRoot_scaleEdge_affine L weight ons_turnRoot
    ons_turnRoot_sq a b q hq t e
  · exact norm_ons_KWmatWeightedPhase_entry_le L
      (ons_scaleEdgeWeight weight (ons_portEdge L e) t) a b q hq
      (norm_ons_scaleEdgeWeight_le weight (ons_portEdge L e) t q hq hweight ht)
  · exact hsmall
  · exact ons_card_mul_lt_one_of_Sherman_small q hsmall

end StatMech.Onsager

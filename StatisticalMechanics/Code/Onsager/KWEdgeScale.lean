/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeighted
import Code.Onsager.FirstReturnScale









namespace StatMech.Onsager

open Matrix BigOperators

def ons_scaleEdgeWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (edge : Sym2 (ZMod L × ZMod L)) (t : ℂ) :
    Sym2 (ZMod L × ZMod L) → ℂ :=
  fun f => if f = edge then t * weight f else weight f

theorem ons_KWmatWeightedPhase_scaleEdge
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega u v t : ℂ) (e : ons_Dart L) :
    ons_KWmatWeightedPhase L
        (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega u v =
      ons_scaleColumns ({e, ons_dartRev L e} : Finset (ons_Dart L)) t
        (ons_KWmatWeightedPhase L weight omega u v) := by
  ext d2 d1
  simp only [ons_KWmatWeightedPhase, ons_KWmatWeighted,
    ons_scaleEdgeWeight, ons_scaleColumns]
  have hedge : ons_portEdge L d1 = ons_portEdge L e ↔
      d1 = e ∨ d1 = ons_dartRev L e :=
    ons_portEdge_eq_iff L e d1
  by_cases hd : d1 = e ∨ d1 = ons_dartRev L e
  · rw [if_pos (hedge.mpr hd)]
    simp only [Finset.mem_insert, Finset.mem_singleton, hd, if_true]
    split <;> ring
  · rw [if_neg (fun h => hd (hedge.mp h))]
    simp only [Finset.mem_insert, Finset.mem_singleton, hd, if_false]

theorem ons_mask_scaleColumns
    {E : Type*} [DecidableEq E]
    (forbidden S : Finset E) (t : ℂ) (Lambda : Matrix E E ℂ) :
    ons_maskMatrix forbidden (ons_scaleColumns S t Lambda) =
      ons_scaleColumns S t (ons_maskMatrix forbidden Lambda) := by
  ext i j
  simp only [ons_maskMatrix, ons_scaleColumns]
  by_cases hf : i ∈ forbidden ∨ j ∈ forbidden
  · simp [hf]
  · simp [hf]

theorem ons_mask_KWmatWeightedPhase_scaleEdge
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega u v t : ℂ) (forbidden : Finset (ons_Dart L))
    (e : ons_Dart L) :
    ons_maskMatrix forbidden
        (ons_KWmatWeightedPhase L
          (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega u v) =
      ons_scaleColumns ({e, ons_dartRev L e} : Finset (ons_Dart L)) t
        (ons_maskMatrix forbidden
          (ons_KWmatWeightedPhase L weight omega u v)) := by
  rw [ons_KWmatWeightedPhase_scaleEdge]
  apply ons_mask_scaleColumns

theorem ons_tsum_firstReturnWeight_scaleEdge
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega u v t : ℂ) (forbidden : Finset (ons_Dart L))
    (e : ons_Dart L) :
    (∑' s, ons_firstReturnWeight
        (ons_maskMatrix forbidden
          (ons_KWmatWeightedPhase L
            (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega u v))
        e (ons_dartRev L e) s) =
      t * ∑' s, ons_firstReturnWeight
        (ons_maskMatrix forbidden
          (ons_KWmatWeightedPhase L weight omega u v))
        e (ons_dartRev L e) s := by
  rw [ons_mask_KWmatWeightedPhase_scaleEdge,
    ons_tsum_firstReturnWeight_scale]

end StatMech.Onsager

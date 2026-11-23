/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeighted
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.FirstReturnScale

/-!

# Scaling one edge weight of a Kac-Ward matrix

Scaling the weight of a single torus edge scales the columns of its two darts, and hence
first-return weights at those darts.

## i. Overview

Multiplying the weight of one torus edge by `t` multiplies the columns of the edge-weighted twisted
Kac-Ward matrix indexed by the two darts of that edge. With `FirstReturnScale`, the total
first-return weight at such a dart (with the other darts suitably masked) is multiplied by `t`.

## ii. Key results

- `ons_scaleEdgeWeight` : the weight function with one edge scaled
- `ons_KWmatWeightedPhase_scaleEdge` : edge scaling is column scaling
- `ons_tsum_firstReturnWeight_scaleEdge` : its effect on first-return weights

## iii. Table of contents

- A. Edge scaling

## iv. References

- None; the material is standard.

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators

/-! ## A. Edge scaling -/

/-- The edge weight function with the weight of `edge` multiplied by `t`. -/
def ons_scaleEdgeWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (edge : Sym2 (ZMod L × ZMod L)) (t : ℂ) :
    Sym2 (ZMod L × ZMod L) → ℂ :=
  fun f => if f = edge then t * weight f else weight f

lemma ons_KWmatWeightedPhase_scaleEdge
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
  · rw [ite_eq_left (hedge.mpr hd)]
    simp only [Finset.mem_insert, Finset.mem_singleton, hd, ite_true]
    split <;> ring
  · rw [ite_eq_right (fun h => hd (hedge.mp h))]
    simp only [Finset.mem_insert, Finset.mem_singleton, hd, ite_false]

lemma ons_mask_scaleColumns
    {E : Type*} [DecidableEq E]
    (forbidden S : Finset E) (t : ℂ) (Lambda : Matrix E E ℂ) :
    ons_maskMatrix forbidden (ons_scaleColumns S t Lambda) =
      ons_scaleColumns S t (ons_maskMatrix forbidden Lambda) := by
  ext i j
  simp only [ons_maskMatrix, ons_scaleColumns]
  by_cases hf : i ∈ forbidden ∨ j ∈ forbidden
  · simp [hf]
  · simp [hf]

lemma ons_mask_KWmatWeightedPhase_scaleEdge
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

lemma ons_tsum_firstReturnWeight_scaleEdge
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

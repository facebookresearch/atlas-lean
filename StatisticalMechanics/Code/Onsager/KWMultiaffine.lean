/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeightedDeletion
import Code.Onsager.KWEdgeScale









namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_mask_scaleColumns_absorb
    {E : Type*} [DecidableEq E]
    (forbidden S : Finset E) (t : ℂ) (Lambda : Matrix E E ℂ)
    (hsub : S ⊆ forbidden) :
    ons_maskMatrix forbidden (ons_scaleColumns S t Lambda) =
      ons_maskMatrix forbidden Lambda := by
  ext i j
  simp only [ons_maskMatrix, ons_scaleColumns]
  by_cases hf : i ∈ forbidden ∨ j ∈ forbidden
  · simp [hf]
  · have hjF : j ∉ forbidden := by tauto
    have hjS : j ∉ S := fun h => hjF (hsub h)
    simp [hf, hjS]

theorem ons_detWalkRoot_scaleEdge_affine
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (q : ℝ) (hq : 0 ≤ q)
    (t : ℂ) (e : ons_Dart L)
    (hentryScaled : ∀ d2 d1,
      ‖ons_KWmatWeightedPhase L
        (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega
        (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_detWalkRoot
        (ons_KWmatWeightedPhase L
          (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
          (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L))
            (ons_KWmatWeightedPhase L weight omega
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_KWmatWeightedPhase L weight omega
            (ons_spinPhase L a) (ons_spinPhase L b))
          e (ons_dartRev L e) s) := by
  let M := ons_KWmatWeightedPhase L weight omega
    (ons_spinPhase L a) (ons_spinPhase L b)
  let Mt := ons_KWmatWeightedPhase L
    (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega
    (ons_spinPhase L a) (ons_spinPhase L b)
  change ons_detWalkRoot Mt =
    ons_detWalkRoot
        (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) M) *
      (1 - t * ∑' s, ons_firstReturnWeight M e (ons_dartRev L e) s)
  have hdel := ons_detWalkRoot_weighted_mask_delete_pair
    L (ons_scaleEdgeWeight weight (ons_portEdge L e) t)
      omega homega a b q hq hentryScaled hsmall hcard
      (∅ : Finset (ons_Dart L)) (by simp) e
  have hmaskempty (A : Matrix (ons_Dart L) (ons_Dart L) ℂ) :
      ons_maskMatrix (∅ : Finset (ons_Dart L)) A = A := by
    ext d2 d1
    simp [ons_maskMatrix]
  rw [hmaskempty] at hdel
  simp only [Finset.union_empty] at hdel
  have hscale : Mt =
      ons_scaleColumns ({e, ons_dartRev L e} : Finset (ons_Dart L)) t M := by
    simpa only [M, Mt] using ons_KWmatWeightedPhase_scaleEdge
      L weight omega (ons_spinPhase L a) (ons_spinPhase L b) t e
  have hmask :
      ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) Mt =
        ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) M := by
    rw [hscale]
    exact ons_mask_scaleColumns_absorb _ _ _ _ Finset.Subset.rfl
  have hsum :
      (∑' s, ons_firstReturnWeight Mt e (ons_dartRev L e) s) =
        t * ∑' s, ons_firstReturnWeight M e (ons_dartRev L e) s := by
    simpa only [M, Mt] using ons_tsum_firstReturnWeight_scaleEdge
      L weight omega (ons_spinPhase L a) (ons_spinPhase L b) t ∅ e
  change ons_detWalkRoot Mt = _ at hdel
  rw [hdel, hmask, hsum]

end StatMech.Onsager

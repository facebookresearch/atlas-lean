/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.SpinWeightedAffine
import Code.Onsager.KWZeroEdge










namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem ons_weightedRoot_eq_spin_scaleEdge_of_coefficient
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (q : ℝ) (hq : 0 ≤ q)
    (hweight : ∀ edge, ‖weight edge‖ ≤ q)
    (t : ℂ) (ht : ‖t‖ ≤ 1) (e : ons_Dart L)
    (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hzero :
      ons_detWalkRoot
          (ons_KWmatWeightedPhase L
            (ons_scaleEdgeWeight weight (ons_portEdge L e) 0) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)) =
        ons_weightedSpinCharacterSum L
          (ons_scaleEdgeWeight weight (ons_portEdge L e) 0) a b)
    (hcoeff :
      ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L e) =
        -ons_detWalkRoot
            (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L))
              (ons_KWmatWeightedPhase L weight ons_turnRoot
                (ons_spinPhase L a) (ons_spinPhase L b))) *
          (∑' s, ons_firstReturnWeight
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))
            e (ons_dartRev L e) s)) :
    ons_detWalkRoot
        (ons_KWmatWeightedPhase L
          (ons_scaleEdgeWeight weight (ons_portEdge L e) t) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_weightedSpinCharacterSum L
        (ons_scaleEdgeWeight weight (ons_portEdge L e) t) a b := by
  have hroot := ons_detWalkRoot_scaleEdge_affine_of_bound
    L weight a b q hq hweight t ht e hsmall
  have hspin := ons_weightedSpinCharacterSum_scaleEdge
    L weight a b (ons_portEdge L e) t
  have hmask := ons_detWalkRoot_zeroEdge_eq_mask L weight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) e
  rw [hmask] at hzero
  rw [hroot, hspin, ← hzero, hcoeff]
  ring

end StatMech.Onsager

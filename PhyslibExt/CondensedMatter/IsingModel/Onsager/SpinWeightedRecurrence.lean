/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinWeightedAffine
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWZeroEdge

/-!

# Recurrence for the edge-weighted root identity

If the root identity holds with one edge weight set to zero and the edge coefficients match, it
holds with that weight restored.

## i. Overview

Both sides of the edge-weighted root identity are affine in a single edge weight `t`: the character
sum is `A + t B` and the Kac-Ward root is `(1 - t λ) R`. If the identity holds at `t = 0` and the
coefficient of `t` agrees (`B = -λ R`), it holds at `t = 1`.

## ii. Key results

- `ons_weightedRoot_eq_spin_scaleEdge_of_coefficient` : one step of the edge-by-edge induction

## iii. Table of contents

- A. The recurrence step

## iv. References

- None; the material is standard.

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

/-! ## A. The recurrence step -/

lemma ons_weightedRoot_eq_spin_scaleEdge_of_coefficient
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

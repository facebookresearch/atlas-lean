/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryIncidenceNoLoop
import Code.FrontierD.FKRectBalancedSectorThermodynamicBridge



open Filter Topology

namespace StatMech.FrontierD

noncomputable section






theorem
    fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_fourCopy
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 ≤ r)
    (heightLower : Nat → Nat)
    (crossingThreshold : (Nat → Nat) → Nat → Nat)
    (hwind : ∀ m : Nat → Nat,
      (∀ k, heightLower k ≤ m k) →
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hsmall : ∀ m : Nat → Nat,
      (∀ k, heightLower k ≤ m k) → ∀ k,
      let R := fkRectFixedChargeVerticalFamily r k (m k)
      let n := crossingThreshold m k
      Nat.choose R.height (n + 1) *
          ((FK.freeInfiniteVolume 2
            (fkRectCriticalP_pos (by linarith : 0 < q))
            (fkRectCriticalP_lt_one (by linarith : 0 < q))
            (by linarith : 0 < q) :
              MeasureTheory.Measure (ConfigSpace
                (Sym2 (StatMech.Lattice.Site 2)))).real
            (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤
        FK.cFE (fkRectCriticalP q) q ^
          (2 * R.width + R.height) / 2)
    (hwidth : ∀ m : Nat → Nat,
      (∀ k, heightLower k ≤ m k) →
      Tendsto (fun k =>
        ((fkRectFixedChargeVerticalFamily r k (m k)).width : Real) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0))
    (hthreshold : ∀ m : Nat → Nat,
      (∀ k, heightLower k ≤ m k) →
      Tendsto (fun k =>
        (crossingThreshold m k : Real) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0))
    (hheight : ∀ m : Nat → Nat,
      (∀ k, heightLower k ≤ m k) →
      Tendsto (fun k =>
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop atTop)
    (hfourCopy : ∀ m : Nat → Nat,
      (∀ k, heightLower k ≤ m k) →
      Tendsto (fun k =>
        fkRectFourCopyShareCost
            (fkRectFixedChargeVerticalFamily r k (m k)) q /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv ≤
      (r : Real) * fkQgt4SixVertexGapRate q := by
  apply fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_fourCopy
    hq r hr heightLower hwind
  · intro m hm
    exact
      tendsto_allSectorNormalization_negLog_div_height_zero_of_boundaryIncidenceAdaptiveTail
        (fun k => fkRectFixedChargeVerticalFamily r k (m k)) hq
        (crossingThreshold m) (hsmall m hm) (hwidth m hm)
        (hthreshold m hm) (hheight m hm)
  · exact hfourCopy

end

end StatMech.FrontierD

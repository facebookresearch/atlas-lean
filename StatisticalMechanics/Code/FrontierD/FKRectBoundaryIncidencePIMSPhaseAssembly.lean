/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule
import Code.FrontierD.FKQgt4PIMSTwoByOnePhaseAssembly










open Filter MeasureTheory Topology

namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section




structure FKQgt4BoundaryIncidenceScheduledFourCopy
    (q xiInv : Real) : Prop where
  winding : forall r : Nat, 2 ≤ r -> forall m : Nat → Nat,
    (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) ->
    Tendsto (fun k =>
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds (((r - 1 : Nat) : Real) * xiInv))
  fourCopy : forall r : Nat, 2 ≤ r -> forall m : Nat → Nat,
    (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) ->
    Tendsto (fun k =>
      fkRectFourCopyShareCost
          (fkRectFixedChargeVerticalFamily r k (m k)) q /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds 0)



theorem
    fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_evenTwoByOneCrossingFloor
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale)) :
    0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq := by
  apply fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_gapRate_le hq
  exact
    fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenTwoByOneCrossingFloor
      hq hhard hcross




theorem
    fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale)) :
    let mu := (FK.freeInfiniteVolume 2
      (fkRectCriticalP_pos (by linarith : 0 < q))
      (fkRectCriticalP_lt_one (by linarith : 0 < q))
      (by linarith : 0 < q) :
        Measure (ConfigSpace (Sym2 (Site 2))))
    mu.real (percolationEvent 2) = 0 := by
  have hpos :=
    fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_evenTwoByOneCrossingFloor
      hq hhard hcross
  have hzero := fkQgt4CriticalFreeTheta_eq_zero_of_exactDiagonalRatePos hq hpos
  simpa [FK.fkThetaFree, fkRectCriticalP] using hzero




theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hscheduled : FKQgt4BoundaryIncidenceScheduledFourCopy q
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  apply fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_fourCopy
    hq r hr
  · exact
      fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor
        hq hhard hcross
  · exact hscheduled.winding r hr
  · exact hscheduled.fourCopy r hr




theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hscheduled : FKQgt4BoundaryIncidenceScheduledFourCopy q
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
          (hasInfiniteClusterEvent 2) = 1 ∧
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) ∧
      0 < fkQgt4SixVertexGapRate q := by
  apply fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_winding
    hq hhard hcross
  exact
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS
      hq hhard hcross hscheduled

end

end StatMech.FrontierD

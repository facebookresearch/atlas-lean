/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedOrbitInteraction
import Code.FrontierD.FKRectRefinedSupportInteraction










namespace StatMech.FrontierD

noncomputable section



theorem fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e : R.EdgeIndex)
    (hopen : pairing d.1 =
      !fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1))
    (hc : FKRectRefinedEdgeCenterNormal
      (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1)) c) :
    fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
  unfold fkRectRefinedBoundaryLocalInteraction
  rw [hopen, fkRectRefinedPrimalEdgeDarts_eq_centerline]
  exact fkRectRefinedLocalDarts_open_interaction_of_normalCenters
    R
    (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1))
    (fkRectClosedPairingAtEdge e) c
    (fkRectRefinedPrimalEdgeCenter R e) d.2 hc
    (fkRectRefinedPrimalEdgeCenter_normal R e)



theorem fkRectRefinedBoundaryLocalInteraction_eq_zero_of_endpointDisjoint
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e : R.EdgeIndex)
    (hdisj : ∀ p,
      FKRectDartListUsesPoint
          ((fkRectRefinedLocalDarts (pairing d.1) c d.2).map
            (fkRectIntegralSquareDartMod
              (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p →
        ¬ FKRectDartListUsesPoint
          ((fkRectRefinedPrimalEdgeDarts R e).map
            (fkRectIntegralSquareDartMod
              (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p) :
    fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
  unfold fkRectRefinedBoundaryLocalInteraction
  exact fkRectRefinedRawInteraction_eq_zero_of_endpointDisjoint _ _ hdisj



theorem fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open_or_disjoint
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e : R.EdgeIndex)
    (hc : FKRectRefinedEdgeCenterNormal
      (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1)) c)
    (hzero :
      pairing d.1 =
          !fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1) ∨
        ∀ p,
          FKRectDartListUsesPoint
              ((fkRectRefinedLocalDarts (pairing d.1) c d.2).map
                (fkRectIntegralSquareDartMod
                  (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p →
            ¬ FKRectDartListUsesPoint
              ((fkRectRefinedPrimalEdgeDarts R e).map
                (fkRectIntegralSquareDartMod
                  (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p) :
    fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
  rcases hzero with hopen | hdisj
  · exact fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open
      R pairing d c e hopen hc
  · exact
      fkRectRefinedBoundaryLocalInteraction_eq_zero_of_endpointDisjoint
        R pairing d c e hdisj

end

end StatMech.FrontierD

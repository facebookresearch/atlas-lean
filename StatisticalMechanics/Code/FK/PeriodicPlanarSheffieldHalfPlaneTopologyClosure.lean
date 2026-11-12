/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneCage








open MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair



def threeCrossingCageEvent
    (D : PeriodicPlanarDualPair P Pdual)
    (B r R C D0 A Tbottom Ttop : Real) :
    Set (ConfigSpace (Sym2 V)) :=
  D.primalEmbedding.verticalCrossingEvent
      (A + 4 * B) (R - 4 * B) (C - 4 * B) (D0 + 4 * B) ∩
    D.primalEmbedding.horizontalCrossingEvent
      (r - 5 * B) (R + 5 * B) (C + 4 * B) (Tbottom - 4 * B) ∩
    D.primalEmbedding.horizontalCrossingEvent
      (r - 5 * B) (R + 5 * B) (Ttop + 4 * B) (D0 - 4 * B)



theorem threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster
    (D : PeriodicPlanarDualPair P Pdual)
    {B r R C D0 A Tbottom Ttop c d : Real}
    (hBpos : 0 < B)
    (hBp : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc huv t - D.primalEmbedding.vertex u) i| ≤ B)
    (hBd : ∀ {u v : W} (huv : Pdual.graph.Adj u v) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc huv t - D.dualEmbedding.vertex u) i| ≤ B)
    (hrR : r < R) (hRightWidth : A + 10 * B < R)
    (hBottom : C + 10 * B < Tbottom)
    (hTop : Ttop + 10 * B < D0)
    (hrootRight : r + B ≤ A)
    (hrootBottom : Tbottom < c) (hrootTop : d < Ttop)
    (hrectBottom : C ≤ c) (hrectTop : d ≤ D0) :
    Disjoint (threeCrossingCageEvent D B r R C D0 A Tbottom Ttop)
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
          r c d) := by
  rw [Set.disjoint_left]
  intro omega hcage hdual
  rcases hcage with ⟨⟨hRightCrossing, hBottomCrossing⟩, hTopCrossing⟩
  change dualConfigEquiv D.edgeDual omega ∈
    D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster r c d at hdual
  obtain ⟨x, hxBoundary, hxc, hxd, hxInfinite⟩ := hdual
  have hxCoordRight : D.dualEmbedding.vertexCoord x 0 < r + B :=
    D.dualEmbedding.rightHalfPlaneBoundary_coord_lt hBd hxBoundary
  have hxRight : D.dualEmbedding.vertexCoord x 0 < A :=
    hxCoordRight.trans_le hrootRight
  have hAR : A < R := by linarith
  have hxRect : x ∈ D.dualEmbedding.rectVertices r R C D0 := by
    refine ⟨hxBoundary.1, ?_, hrectBottom.trans hxc, hxd.trans hrectTop⟩
    exact (hxRight.trans hAR).le
  have hnot :=
    D.not_infiniteComplementaryDualClusterWithin_rightHalfPlane_of_threeCrossings
      omega hBpos hBp hBd hrR hRightWidth hBottom hTop hxRect hxRight
        (hrootBottom.trans_le hxc) (hxd.trans_lt hrootTop)
        hRightCrossing hBottomCrossing hTopCrossing
  exact hnot hxInfinite




theorem finiteJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage
    (D : PeriodicPlanarDualPair P Pdual)
    {B r R C D0 A Tbottom Ttop c d : Real}
    (hBpos : 0 < B)
    (hBp : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc huv t - D.primalEmbedding.vertex u) i| ≤ B)
    (hBd : ∀ {u v : W} (huv : Pdual.graph.Adj u v) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc huv t - D.dualEmbedding.vertex u) i| ≤ B)
    (hrR : r < R) (hRightWidth : A + 10 * B < R)
    (hBottom : C + 10 * B < Tbottom)
    (hTop : Ttop + 10 * B < D0)
    (hrootRight : r + B ≤ A)
    (hrootBottom : Tbottom < c) (hrootTop : d < Ttop)
    (hrectBottom : C ≤ c) (hrectTop : d ≤ D0)
    {rPrimal cPrimal dPrimal : Real} {n : Nat} {L U : Finset V}
    (hjoined : D.primalEmbedding.finiteJoinedBoundaryArmEvent
      rPrimal cPrimal dPrimal n L U ⊆
        threeCrossingCageEvent D B r R C D0 A Tbottom Ttop) :
    Disjoint
      (D.primalEmbedding.finiteJoinedBoundaryArmEvent
        rPrimal cPrimal dPrimal n L U)
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
          r c d) := by
  have hcage :=
    D.threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster
      hBpos hBp hBd hrR hRightWidth hBottom hTop hrootRight
        hrootBottom hrootTop hrectBottom hrectTop
  rw [Set.disjoint_left] at hcage ⊢
  exact fun omega homega hdual => hcage (hjoined homega) hdual

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

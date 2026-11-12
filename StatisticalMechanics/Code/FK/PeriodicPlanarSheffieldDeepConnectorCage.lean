/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldDeepConnector
import Code.FK.PeriodicPlanarSheffieldHalfPlaneTopologyClosure










open Filter MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



def PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P) (r R c d : Real) (width : Nat)
    (L U : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
      (E.lowerBoundaryRayVertices r c) ∩
    E.infiniteOpenBoundaryConnectionTo r (U : Set V)
      (E.upperBoundaryRayVertices r d)) \
    E.halfPlaneStripPairMergeErrorUnion R width L U

theorem PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (r R c d : Real) (width : Nat)
    (L U : Finset V) :
    MeasurableSet
      (E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) :=
  ((E.infiniteOpenBoundaryConnectionTo_measurableSet r (L : Set V)
      (E.lowerBoundaryRayVertices r c)).inter
    (E.infiniteOpenBoundaryConnectionTo_measurableSet r (U : Set V)
      (E.upperBoundaryRayVertices r d))).diff
    (E.halfPlaneStripPairMergeErrorUnion_measurableSet R width L U)



theorem PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_witnesses
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r R c d : Real} {width : Nat} {L U : Finset V}
    (h : omega ∈
      E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) :
    ∃ x ∈ L, (P.cluster omega x).Infinite ∧
      ∃ b ∈ E.lowerBoundaryRayVertices r c,
        omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧
      ∃ y ∈ U, (P.cluster omega y).Infinite ∧
        ∃ u ∈ E.upperBoundaryRayVertices r d,
          omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧
          omega ∈ P.connectedWithinSet
            (E.rightHalfPlaneStripVertices R width) x y := by
  rcases h.1.1 with
    ⟨x, hxL, hxInfinite, b, hbLower, _hbBoundary,
      _z, _hbz, _hz, _hbzOpen, hxb⟩
  rcases h.1.2 with
    ⟨y, hyU, hyInfinite, u, huUpper, _huBoundary,
      _w, _huw, _hw, _huwOpen, hyu⟩
  have hxy : omega ∈
      P.connectedWithinSet (E.rightHalfPlaneStripVertices R width) x y := by
    by_contra hnot
    apply h.2
    rw [PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion]
    apply Set.mem_iUnion.2
    refine ⟨⟨(x, y), Finset.mem_product.2 ⟨hxL, hyU⟩⟩, ?_⟩
    exact ⟨⟨hxInfinite, hyInfinite⟩, hnot⟩
  exact ⟨x, hxL, hxInfinite, b, hbLower, hxb,
    y, hyU, hyInfinite, u, huUpper, hyu, hxy⟩



theorem PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_verticalCrossing
    (E : PeriodicPlaneEmbedding P)
    {B r R c d cRight dRight : Real} {width : Nat} {L U : Finset V}
    (hB : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hvw t - E.vertex v) i| ≤ B)
    (hB0 : 0 ≤ B) (hgap : cRight + B < dRight)
    (hLbelow : ∀ x ∈ L, E.vertexCoord x 1 < cRight)
    (hUabove : ∀ y ∈ U, dRight < E.vertexCoord y 1) :
    E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U ⊆
      E.verticalCrossingEvent R (R + width) cRight dRight := by
  intro omega homega
  obtain ⟨x, hxL, _hxInfinite, _b, _hbLower, _hxb,
    y, hyU, _hyInfinite, _u, _huUpper, _hyu, hxy⟩ :=
      E.finiteDeepOpenExitedJoinedBoundaryArmEvent_witnesses homega
  obtain ⟨p, hpStrip⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  apply E.verticalCrossingEvent_of_openWalk omega hB hB0 hgap p
    (hLbelow x hxL) (hUabove y hyU)
  intro v hv
  exact hpStrip v hv


theorem PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_ge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r R c d : Real) (width : Nat) (L U : Finset V) :
    mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
        (E.lowerBoundaryRayVertices r c)) +
      mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V)
        (E.upperBoundaryRayVertices r d)) -
      mu.real (E.halfPlaneStripPairMergeErrorUnion R width L U) - 1 ≤
        mu.real (E.finiteDeepOpenExitedJoinedBoundaryArmEvent
          r R c d width L U) := by
  let A := E.infiniteOpenBoundaryConnectionTo r (L : Set V)
    (E.lowerBoundaryRayVertices r c)
  let Bset := E.infiniteOpenBoundaryConnectionTo r (U : Set V)
    (E.upperBoundaryRayVertices r d)
  let C := E.halfPlaneStripPairMergeErrorUnion R width L U
  have hthree := three_event_intersection_lower_bound mu
    (E.infiniteOpenBoundaryConnectionTo_measurableSet r (U : Set V)
      (E.upperBoundaryRayVertices r d))
    (E.halfPlaneStripPairMergeErrorUnion_measurableSet R width L U).compl
    (A := A) (B := Bset) (C := Cᶜ)
  have hC : mu.real Cᶜ = 1 - mu.real C := by
    rw [measureReal_compl
      (E.halfPlaneStripPairMergeErrorUnion_measurableSet R width L U),
      probReal_univ]
  rw [hC] at hthree
  change mu.real A + mu.real Bset - mu.real C - 1 ≤
    mu.real ((A ∩ Bset) \ C)
  convert hthree using 1 <;> ring



theorem PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r R c d : Nat → Real) (width : Nat → Nat)
    (L U : Nat → Finset V)
    (hlower : Tendsto (fun n =>
      mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (L n : Set V)
        (E.lowerBoundaryRayVertices (r n) (c n)))) atTop (nhds 1))
    (hupper : Tendsto (fun n =>
      mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (U n : Set V)
        (E.upperBoundaryRayVertices (r n) (d n)))) atTop (nhds 1))
    (hmerge : Tendsto (fun n => mu.real
      (E.halfPlaneStripPairMergeErrorUnion
        (R n) (width n) (L n) (U n))) atTop (nhds 0)) :
    Tendsto (fun n => mu.real
      (E.finiteDeepOpenExitedJoinedBoundaryArmEvent
        (r n) (R n) (c n) (d n) (width n) (L n) (U n)))
      atTop (nhds 1) := by
  have hlowerBound : Tendsto (fun n =>
      mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (L n : Set V)
          (E.lowerBoundaryRayVertices (r n) (c n))) +
        mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (U n : Set V)
          (E.upperBoundaryRayVertices (r n) (d n))) -
        mu.real (E.halfPlaneStripPairMergeErrorUnion
          (R n) (width n) (L n) (U n)) - 1) atTop (nhds 1) := by
    simpa using ((hlower.add hupper).sub hmerge).sub
      (tendsto_const_nhds (x := (1 : Real)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerBound tendsto_const_nhds
      (fun n => E.finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_ge
        mu (r n) (R n) (c n) (d n) (width n) (L n) (U n))
      (fun _ => measureReal_le_one)

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair




theorem finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_threeCrossingCageEvent
    (D : PeriodicPlanarDualPair P Pdual)
    {B rPrimal Rdeep rDual Rcage C D0 A Tbottom Ttop c d : Real}
    {width : Nat} {L U : Finset V}
    (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hvw t - D.primalEmbedding.vertex v) i| ≤ B)
    (hB0 : 0 ≤ B) (hRightGap : C - 4 * B + B < D0 + 4 * B)
    (hLbelow : ∀ x ∈ L,
      D.primalEmbedding.vertexCoord x 1 < C - 4 * B)
    (hUabove : ∀ y ∈ U,
      D0 + 4 * B < D.primalEmbedding.vertexCoord y 1)
    (hwidth : A + 4 * B = Rdeep ∧
      Rdeep + width = Rcage - 4 * B)
    (hLowerCorridor :
      D.primalEmbedding.infiniteOpenBoundaryConnectionTo
          rPrimal (L : Set V)
          (D.primalEmbedding.lowerBoundaryRayVertices rPrimal c) ⊆
        D.primalEmbedding.horizontalCrossingEvent
          (rDual - 5 * B) (Rcage + 5 * B)
          (C + 4 * B) (Tbottom - 4 * B))
    (hUpperCorridor :
      D.primalEmbedding.infiniteOpenBoundaryConnectionTo
          rPrimal (U : Set V)
          (D.primalEmbedding.upperBoundaryRayVertices rPrimal d) ⊆
        D.primalEmbedding.horizontalCrossingEvent
          (rDual - 5 * B) (Rcage + 5 * B)
          (Ttop + 4 * B) (D0 - 4 * B)) :
    D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
        rPrimal Rdeep c d width L U ⊆
      threeCrossingCageEvent D B rDual Rcage C D0 A Tbottom Ttop := by
  intro omega homega
  have hRight :=
    D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_verticalCrossing
      hBp hB0 hRightGap hLbelow hUabove homega
  have hLower := hLowerCorridor homega.1.1
  have hUpper := hUpperCorridor homega.1.2
  rw [threeCrossingCageEvent]
  refine ⟨⟨?_, hLower⟩, hUpper⟩
  rw [hwidth.1]
  simpa only [← hwidth.2] using hRight




theorem finiteDeepOpenExitedJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage
    (D : PeriodicPlanarDualPair P Pdual)
    {B rPrimal Rdeep rDual Rcage C D0 A Tbottom Ttop c d : Real}
    {width : Nat} {L U : Finset V}
    (hBpos : 0 < B)
    (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hvw t - D.primalEmbedding.vertex v) i| ≤ B)
    (hBd : ∀ {v w : W} (hvw : Pdual.graph.Adj v w) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hvw t - D.dualEmbedding.vertex v) i| ≤ B)
    (hrR : rDual < Rcage) (hRightWidth : A + 10 * B < Rcage)
    (hBottom : C + 10 * B < Tbottom)
    (hTop : Ttop + 10 * B < D0)
    (hrootRight : rDual + B ≤ A)
    (hrootBottom : Tbottom < c) (hrootTop : d < Ttop)
    (hrectBottom : C ≤ c) (hrectTop : d ≤ D0)
    (hsubset :
      D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
          rPrimal Rdeep c d width L U ⊆
        threeCrossingCageEvent
          D B rDual Rcage C D0 A Tbottom Ttop) :
    Disjoint
      (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
        rPrimal Rdeep c d width L U)
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
          rDual c d) := by
  have hcage :=
    D.threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster
      hBpos hBp hBd hrR hRightWidth hBottom hTop hrootRight
        hrootBottom hrootTop hrectBottom hrectTop
  rw [Set.disjoint_left] at hcage ⊢
  exact fun omega homega hdual => hcage (hsubset homega) hdual

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

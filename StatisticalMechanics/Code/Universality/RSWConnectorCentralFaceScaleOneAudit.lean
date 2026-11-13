/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorCentralFaceFiniteGraph










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

private def axisReturn_v0 : rect (-2) 0 (-1) 1 :=
  ⟨![-2, 0], by simp [mem_rect]⟩

private def axisReturn_v1 : rect (-2) 0 (-1) 1 :=
  ⟨![-2, 1], by simp [mem_rect]⟩

private def axisReturn_v2 : rect (-2) 0 (-1) 1 :=
  ⟨![-1, 1], by simp [mem_rect]⟩

private def axisReturn_v3 : rect (-2) 0 (-1) 1 :=
  ⟨![-1, 0], by simp [mem_rect]⟩

private def axisReturn_v4 : rect (-2) 0 (-1) 1 :=
  ⟨![0, 0], by simp [mem_rect]⟩

private def axisReturn_v5 : rect (-2) 0 (-1) 1 :=
  ⟨![0, 1], by simp [mem_rect]⟩

private theorem axisReturn_adj01 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v0 axisReturn_v1 := by
  simp [axisReturn_v0, axisReturn_v1, hypercubicLattice_adj]

private theorem axisReturn_adj12 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v1 axisReturn_v2 := by
  simp [axisReturn_v1, axisReturn_v2, hypercubicLattice_adj]

private theorem axisReturn_adj23 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v2 axisReturn_v3 := by
  simp [axisReturn_v2, axisReturn_v3, hypercubicLattice_adj]

private theorem axisReturn_adj34 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v3 axisReturn_v4 := by
  simp [axisReturn_v3, axisReturn_v4, hypercubicLattice_adj]

private theorem axisReturn_adj45 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v4 axisReturn_v5 := by
  simp [axisReturn_v4, axisReturn_v5, hypercubicLattice_adj]

private def axisReturn_walk :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Walk
      axisReturn_v0 axisReturn_v5 :=
  .cons axisReturn_adj01
    (.cons axisReturn_adj12
      (.cons axisReturn_adj23
        (.cons axisReturn_adj34 (.cons axisReturn_adj45 .nil))))




noncomputable def rlc_axisReturnCounterexampleLeft :
    RlcLeftDiagonalPath 1 := by
  let x : leftSide (-2) 0 (-1) 1 :=
    ⟨(axisReturn_v0 : Site 2), by
      simp [axisReturn_v0, mem_leftSide, mem_rect]⟩
  let y : rightSide (-2) 0 (-1) 1 :=
    ⟨(axisReturn_v5 : Site 2), by
      simp [axisReturn_v5, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath (-2) 0 (-1) 1 :=
    ⟨x, y, axisReturn_walk.toPath⟩
  exact ⟨p, by simp [p, x, axisReturn_v0, rlc_lowerHalf],
    by simp [p, y, axisReturn_v5, rlc_upperHalf]⟩

theorem rlc_axisReturnCounterexample_left_vertices :
    rlc_pathVertices rlc_axisReturnCounterexampleLeft.1 =
      {![-2, 0], ![-2, 1], ![-1, 1], ![-1, 0], ![0, 0], ![0, 1]} := by
  simp [rlc_axisReturnCounterexampleLeft, rlc_pathVertices,
    axisReturn_walk, axisReturn_v0, axisReturn_v1, axisReturn_v2,
    axisReturn_v3, axisReturn_v4, axisReturn_v5,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

theorem rlc_axisReturnCounterexample_left_edges :
    rlc_pathEdges rlc_axisReturnCounterexampleLeft.1 =
      {s((![-2, 0] : Site 2), ![-2, 1]),
        s((![-2, 1] : Site 2), ![-1, 1]),
        s((![-1, 1] : Site 2), ![-1, 0]),
        s((![-1, 0] : Site 2), ![0, 0]),
        s((![0, 0] : Site 2), ![0, 1])} := by
  simp [rlc_axisReturnCounterexampleLeft, rlc_pathEdges,
    axisReturn_walk, axisReturn_v0, axisReturn_v1, axisReturn_v2,
    axisReturn_v3, axisReturn_v4, axisReturn_v5,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]



theorem rlc_axisReturnCounterexample_bookPositioned :
    RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft := by
  constructor
  · rw [Finset.disjoint_left]
    intro z hzR hzL
    rw [rlc_traceSplitCounterexample_right_vertices] at hzR
    rw [rlc_axisReturnCounterexample_left_vertices] at hzL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzR hzL
    rcases hzR with rfl | rfl | rfl | rfl <;> simp_all
  · change (-1 : Int) < 0
    norm_num
  · change 0 < (1 : Int)
    norm_num



theorem rlc_axisReturnCounterexample_not_bookFaithful :
    ¬ RlcBookFaithfulTracePair rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft := by
  intro h
  have haxis := h.left_axis_unique
    (z := (![0, 0] : Site 2)) (by
      rw [rlc_axisReturnCounterexample_left_vertices]
      simp) (by simp)
  have : (![0, 0] : Site 2) = ![0, 1] := by
    simpa [rlc_axisReturnCounterexampleLeft, axisReturn_v5] using haxis
  have := congrArg (fun z : Site 2 => z 1) this
  norm_num at this



theorem rlc_bookPositioned_not_imply_bookFaithful_scaleOne :
    ¬ (RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight
          rlc_axisReturnCounterexampleLeft ->
        RlcBookFaithfulTracePair rlc_traceSplitCounterexampleRight
          rlc_axisReturnCounterexampleLeft) := by
  intro h
  exact rlc_axisReturnCounterexample_not_bookFaithful
    (h rlc_axisReturnCounterexample_bookPositioned)



theorem rlc_traceSplitCounterexample_bookFaithful :
    RlcBookFaithfulTracePair rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
  refine ⟨rlc_traceSplitCounterexample_bookPositioned, ?_, ?_⟩
  · intro z hz hz0
    rw [rlc_traceSplitCounterexample_right_vertices] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rfl
    · simp at hz0
    · simp at hz0
    · simp at hz0
  · intro z hz hz0
    rw [rlc_traceSplitCounterexample_left_vertices] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simp at hz0
    · simp at hz0
    · simp at hz0
    · rfl



theorem rlc_traceSplitCounterexample_bookFaithfulExtremal :
    RlcBookFaithfulExtremalTracePair rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
  refine ⟨rlc_traceSplitCounterexample_bookFaithful, ?_⟩
  exact ⟨rlc_extremalSelectionCounterexampleConfig,
    rlc_extremalSelection_extremalPairCandidate⟩

private theorem scaleOne_centralFace_south_mem_region :
    (![0, -1] : Site 2) ∈
      rlc_connectorCentralFaceRegion rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  have hs := rlc_connectorCentralFace_mem_faceBox (n := 1) (by norm_num)
  have ht : (![0, -1] : Site 2) ∈ rlc_connectorFaceBox 1 := by
    simp [rlc_connectorFaceBox, mem_rect]
  have hnotBarrier : (![1, 0] : Site 2) ∉
      rlc_connectorBarrier rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
    rw [rlc_connectorBarrier,
      rlc_traceSplitCounterexample_right_vertices,
      rlc_traceSplitCounterexample_left_vertices]
    simp [rlc_flipX, rlc_flipXFun]
  have hshared : sharedPrimalEdge (![0, 0] : Site 2) ![0, -1] =
      s((![0, 0] : Site 2), ![1, 0]) := by
    rw [show (![(0 : Int), -1] : Site 2) = ![0, 0 - 1] by norm_num,
      sharedPrimalEdge_bottom]
    simp [faceCorner00, faceCorner10]
  have hwall : sharedPrimalEdge (![0, 0] : Site 2) ![0, -1] ∉
      rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
    rw [hshared]
    intro he
    exact hnotBarrier
      (rlc_mem_connectorBarrier_of_mem_fourTraceEdge _ _ he
        (Sym2.mem_mk_right _ _))
  have hadj : (rlc_connectorFiniteFaceCutGraph
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft).Adj
        ⟨rlc_connectorCentralFace, hs⟩ ⟨![0, -1], ht⟩ := by
    change (rlc_connectorFourTraceFaceCutGraph
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft).Adj ![0, 0] ![0, -1]
    rw [rlc_connectorFourTraceFaceCutGraph_adj]
    exact ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], hwall⟩
  have hset : (![0, -1] : Site 2) ∈
      rlc_connectorCentralFaceRegionSet rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := ⟨ht, hs, hadj.reachable⟩
  simpa [rlc_connectorCentralFaceRegion] using hset

private theorem scaleOne_closureEdge_mem
    {x y f : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y)
    (hx : x ∈ rlc_connectorBox 1) (hy : y ∈ rlc_connectorBox 1)
    (hf : f ∈ rlc_connectorCentralFaceRegion
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft)
    (hflank : f ∈ flankFaces x y) :
    s(x, y) ∈ rlc_connectorCentralFaceClosureEdges
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  rw [rlc_connectorCentralFaceClosureEdges, Finset.mem_filter]
  refine ⟨?_, ⟨f, hf, ?_⟩⟩
  · rw [mem_edgesWithinFinset]
    exact ⟨x, hx, y, hy, rfl⟩
  · rw [StatMech.FrontierD.fci_faceEdgeEquiv_symm_mk_of_adj hxy]
    exact hflank

private theorem scaleOne_closure_edge_one :
    s((![1, -1] : Site 2), ![1, 0]) ∈
      rlc_connectorCentralFaceClosureEdges
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  apply scaleOne_closureEdge_mem
    (by simp [hypercubicLattice_adj, Fin.sum_univ_two])
    (by simp [rlc_connectorBox, mem_rect])
    (by simp [rlc_connectorBox, mem_rect])
    scaleOne_centralFace_south_mem_region
  simp [flankFaces]

private theorem scaleOne_closure_edge_two :
    s((![1, 0] : Site 2), ![1, 1]) ∈
      rlc_connectorCentralFaceClosureEdges
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  apply scaleOne_closureEdge_mem
    (by simp [hypercubicLattice_adj, Fin.sum_univ_two])
    (by simp [rlc_connectorBox, mem_rect])
    (by simp [rlc_connectorBox, mem_rect])
    (rlc_connectorCentralFace_mem_region _ _ (by norm_num))
  simp [rlc_connectorCentralFace, flankFaces]

private theorem scaleOne_closure_edge_three :
    s((![1, 1] : Site 2), ![0, 1]) ∈
      rlc_connectorCentralFaceClosureEdges
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  apply scaleOne_closureEdge_mem
    (by simp [hypercubicLattice_adj, Fin.sum_univ_two])
    (by simp [rlc_connectorBox, mem_rect])
    (by simp [rlc_connectorBox, mem_rect])
    (rlc_connectorCentralFace_mem_region _ _ (by norm_num))
  rw [flankFaces_comm]
  simp [rlc_connectorCentralFace, flankFaces]

private theorem scaleOne_preimage_not_exposed
    {x y : Site 2}
    (havoid : x ∉ rlc_pathVertices rlc_traceSplitCounterexampleRight.1 ∧
      x ∉ rlc_pathVertices rlc_traceSplitCounterexampleLeft.1) :
    s(x, y) ∉ rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
      rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
  intro he
  rw [Finset.mem_union] at he
  rcases he with hright | hleft
  · exact havoid.1
      (rlc_pathEdge_endpoints_mem_vertices
        rlc_traceSplitCounterexampleRight.1 hright).1
  · exact havoid.2
      (rlc_pathEdge_endpoints_mem_vertices
        rlc_traceSplitCounterexampleLeft.1 hleft).1

private theorem scaleOne_active_lift_closed
    {e : Sym2 (Site 2)}
    (he : e ∉
      ({s((![1, -1] : Site 2), ![1, 0]),
        s((![0, 0] : Site 2), ![1, 0]),
        s((![-1, 0] : Site 2), ![0, 0])} :
          Finset (Sym2 (Site 2)))) :
    ∀ f : Sym2 (RlcConnectorVertex 1),
      f.map Subtype.val = e → rlc_activeGapDoubleFailureConfig f = false := by
  intro f hf
  simp [rlc_activeGapDoubleFailureConfig, hf, he]

private theorem scaleOne_pims_edge_one_open :
    rlc_connectorCentralFacePIMSConfig
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      rlc_activeGapDoubleFailureConfig
      s(⟨![1, -1], by simp [mem_rect]⟩,
        ⟨![1, 0], by simp [mem_rect]⟩) = true := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![1, -1] : Site 2), ![1, 0]) =
        s((![-2, -1] : Site 2), ![-1, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical 1 (-1)
  rw [show (s(⟨![1, -1], by simp [mem_rect]⟩,
      ⟨![1, 0], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![1, -1] : Site 2), ![1, 0]) by rfl, hpims]
  have htrace := scaleOne_preimage_not_exposed
    (x := (![-2, -1] : Site 2)) (y := ![-1, -1]) (by
      rw [rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp)
  rw [rlc_connectorCentralFaceAmbientConfig_eq_false_of_lifts_closed
    _ _ _ htrace (scaleOne_active_lift_closed (by simp))]
  rfl

private theorem scaleOne_pims_edge_two_open :
    rlc_connectorCentralFacePIMSConfig
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      rlc_activeGapDoubleFailureConfig
      s(⟨![1, 0], by simp [mem_rect]⟩,
        ⟨![1, 1], by simp [mem_rect]⟩) = true := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![1, 0] : Site 2), ![1, 1]) =
        s((![-2, 0] : Site 2), ![-1, 0]) := by
    simpa using rlc_pimsEdgeEquiv_vertical 1 0
  rw [show (s(⟨![1, 0], by simp [mem_rect]⟩,
      ⟨![1, 1], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![1, 0] : Site 2), ![1, 1]) by rfl, hpims]
  have htrace := scaleOne_preimage_not_exposed
    (x := (![-1, 0] : Site 2)) (y := ![-2, 0]) (by
      rw [rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp)
  rw [show s((![-2, 0] : Site 2), ![-1, 0]) =
      s((![-1, 0] : Site 2), ![-2, 0]) by rw [Sym2.eq_swap],
    rlc_connectorCentralFaceAmbientConfig_eq_false_of_lifts_closed
      _ _ _ htrace (scaleOne_active_lift_closed (by simp))]
  rfl

private theorem scaleOne_pims_edge_three_open :
    rlc_connectorCentralFacePIMSConfig
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      rlc_activeGapDoubleFailureConfig
      s(⟨![1, 1], by simp [mem_rect]⟩,
        ⟨![0, 1], by simp [mem_rect]⟩) = true := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![0, 1] : Site 2), ![1, 1]) =
        s((![-1, 0] : Site 2), ![-1, 1]) := by
    simpa using rlc_pimsEdgeEquiv_horizontal 0 1
  rw [show (s(⟨![1, 1], by simp [mem_rect]⟩,
      ⟨![0, 1], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![0, 1] : Site 2), ![1, 1]) by
          simp [Sym2.map_mk, Sym2.eq_swap], hpims]
  have htrace := scaleOne_preimage_not_exposed
    (x := (![-1, 0] : Site 2)) (y := ![-1, 1]) (by
      rw [rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp)
  rw [rlc_connectorCentralFaceAmbientConfig_eq_false_of_lifts_closed
    _ _ _ htrace (scaleOne_active_lift_closed (by simp))]
  rfl




theorem rlc_activeDoubleFailure_centralFaceClosurePIMS_success :
    rlc_connectorCentralFacePIMSConfig
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
        rlc_activeGapDoubleFailureConfig ∈
      rlc_finiteCentralFaceClosureConnectorEvent
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  let a : RlcConnectorVertex 1 := ⟨![1, -1], by simp [mem_rect]⟩
  let b : RlcConnectorVertex 1 := ⟨![1, 0], by simp [mem_rect]⟩
  let c : RlcConnectorVertex 1 := ⟨![1, 1], by simp [mem_rect]⟩
  let d : RlcConnectorVertex 1 := ⟨![0, 1], by simp [mem_rect]⟩
  refine ⟨a, d, ?_, ?_, ?_⟩
  · rw [rlc_connectorOnRight,
      rlc_traceSplitCounterexample_right_vertices]
    simp [a]
  · rw [rlc_connectorOnLeft,
      rlc_traceSplitCounterexample_left_vertices]
    simp [d]
  · have hab : (FK.openSub (rlc_connectorCentralFaceClosureGraph
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft)
        (rlc_connectorCentralFacePIMSConfig
          rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
          rlc_activeGapDoubleFailureConfig)).Adj a b := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [a, b, hypercubicLattice_adj, Fin.sum_univ_two]
      · simpa [rlc_connectorCentralFacePlanarEdges, a, b] using
          (Finset.mem_union_left
          (rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
            rlc_traceSplitCounterexampleLeft) scaleOne_closure_edge_one)
      · simpa [a, b] using scaleOne_pims_edge_one_open
    have hbc : (FK.openSub (rlc_connectorCentralFaceClosureGraph
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft)
        (rlc_connectorCentralFacePIMSConfig
          rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
          rlc_activeGapDoubleFailureConfig)).Adj b c := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [b, c, hypercubicLattice_adj, Fin.sum_univ_two]
      · simpa [rlc_connectorCentralFacePlanarEdges, b, c] using
          (Finset.mem_union_left
          (rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
            rlc_traceSplitCounterexampleLeft) scaleOne_closure_edge_two)
      · simpa [b, c] using scaleOne_pims_edge_two_open
    have hcd : (FK.openSub (rlc_connectorCentralFaceClosureGraph
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft)
        (rlc_connectorCentralFacePIMSConfig
          rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
          rlc_activeGapDoubleFailureConfig)).Adj c d := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [c, d, hypercubicLattice_adj, Fin.sum_univ_two]
      · simpa [rlc_connectorCentralFacePlanarEdges, c, d, Sym2.eq_swap] using
          (Finset.mem_union_left
          (rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
            rlc_traceSplitCounterexampleLeft) scaleOne_closure_edge_three)
      · simpa [c, d] using scaleOne_pims_edge_three_open
    exact hab.reachable.trans (hbc.reachable.trans hcd.reachable)

end

end StatMech.Universality

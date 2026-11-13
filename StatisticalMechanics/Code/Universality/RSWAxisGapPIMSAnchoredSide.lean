/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWAxisGapPIMSSelectedSide










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section




structure RlcAxisGapPIMSAnchoredContourCore {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) where
  lowerAxis : Site 2
  upperAxis : Site 2
  firstFace : Site 2
  secondFace : Site 2
  baseFace : Site 2
  contour : (faceBoundaryGraph
    (rlc_axisGapReachSet G (rlc_axisGapAmbientConfig G tau))).Walk
      baseFace baseFace
  axis_boundary : (lowerAxis, upperAxis) ∈ edgeBoundary 2
    (rlc_axisGapReachSet G (rlc_axisGapAmbientConfig G tau))
  lowerAxis_zero : lowerAxis 0 = 0
  upperAxis_zero : upperAxis 0 = 0
  anchor_adj : (faceBoundaryGraph
    (rlc_axisGapReachSet G (rlc_axisGapAmbientConfig G tau))).Adj
      firstFace secondFace
  anchor_shared : sharedPrimalEdge firstFace secondFace =
    s(lowerAxis, upperAxis)
  contour_isCycle : contour.IsCycle
  anchor_mem : s(firstFace, secondFace) ∈ contour.edges



theorem rlc_axisGapPIMSAnchoredContourCore_of_failure {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    Nonempty (RlcAxisGapPIMSAnchoredContourCore G tau) := by
  have hamb : rlc_axisGapAmbientConfig G tau ∉
      rlc_axisGapConnectorEvent G := by
    intro hconn
    exact hno
      ((rlc_axisGapAmbientConfig_mem_connectorEvent_iff G tau).mp hconn)
  obtain ⟨p, q, f, g, u, c, hpq, hp0, hq0, hfg,
      hshared, hcycle, hedge⟩ :=
    rlc_axisGapReachSet_axis_anchored_dualCircuit
      G (rlc_axisGapAmbientConfig G tau) hamb
  exact ⟨{
    lowerAxis := p
    upperAxis := q
    firstFace := f
    secondFace := g
    baseFace := u
    contour := c
    axis_boundary := hpq
    lowerAxis_zero := hp0
    upperAxis_zero := hq0
    anchor_adj := hfg
    anchor_shared := hshared
    contour_isCycle := hcycle
    anchor_mem := hedge
  }⟩




structure RlcAxisGapPIMSAnchoredSelectedSide {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (C : RlcAxisGapPIMSAnchoredContourCore G tau) where
  rightContact : Site 2
  leftContact : Site 2
  right_mem : rightContact ∈ C.contour.support
  left_mem : leftContact ∈ C.contour.support
  right_trace : rlc_dualReflect rightContact ∈
    rlc_pathVertices gamma.1
  left_trace : rlc_dualReflect leftContact ∈
    rlc_pathVertices gamma'.1
  supportedSide :
    let eta := rlc_maskConfig (rlc_axisGapEdges G)
      (rlc_axisGapAmbientConfig G tau)
    let hle := rlc_axisGapFaceBoundaryGraph_le_openFaceDual
      G hn hlt (rlc_axisGapAmbientConfig G tau)
    (∀ e ∈ (rlc_dualReflectOpenWalk eta
      ((rlc_orderedContourArc C.contour right_mem left_mem).mapLe hle)).edges,
      e ∈ rlc_axisGapEdges G) ∨
    ∀ e ∈ (rlc_dualReflectOpenWalk eta
      ((rlc_complementaryContourArc C.contour
        right_mem left_mem).mapLe hle)).edges,
      e ∈ rlc_axisGapEdges G



def RlcAxisGapPIMSAnchoredSideExists {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ C : RlcAxisGapPIMSAnchoredContourCore G tau,
    Nonempty (RlcAxisGapPIMSAnchoredSelectedSide G hn hlt tau C)



theorem rlc_axisGapPIMSBoundaryArc_of_anchoredSelectedSide {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {C : RlcAxisGapPIMSAnchoredContourCore G tau}
    (hside : RlcAxisGapPIMSAnchoredSelectedSide G hn hlt tau C) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
  rcases hside.supportedSide with hforward | hbackward
  · exact ⟨hside.rightContact, hside.leftContact,
      rlc_orderedContourArc C.contour hside.right_mem hside.left_mem,
      hside.right_trace, hside.left_trace, hforward⟩
  · exact ⟨hside.rightContact, hside.leftContact,
      rlc_complementaryContourArc C.contour
        hside.right_mem hside.left_mem,
      hside.right_trace, hside.left_trace, hbackward⟩


theorem rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hside : RlcAxisGapPIMSAnchoredSideExists G hn hlt tau) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
  obtain ⟨C, hC⟩ := hside
  obtain ⟨hselected⟩ := hC
  exact rlc_axisGapPIMSBoundaryArc_of_anchoredSelectedSide
    G hn hlt tau hselected



def RlcAxisGapPIMSFailureSelectedSideTopology {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) : Prop :=
  ∀ tau : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    tau ∉ rlc_finiteAxisGapConnectorEvent G →
      RlcAxisGapPIMSAnchoredSideExists G hn hlt tau




def RlcAxisGapPIMSAnchoredContourSelector {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) : Prop :=
  ∀ (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))),
    tau ∉ rlc_finiteAxisGapConnectorEvent G →
      ∀ C : RlcAxisGapPIMSAnchoredContourCore G tau,
        Nonempty (RlcAxisGapPIMSAnchoredSelectedSide G hn hlt tau C)



theorem rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (hselector : RlcAxisGapPIMSAnchoredContourSelector G hn hlt) :
    RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt := by
  intro tau hno
  obtain ⟨C⟩ := rlc_axisGapPIMSAnchoredContourCore_of_failure G tau hno
  exact ⟨C, hselector tau hno C⟩



theorem rlc_axisGapPIMS_success_of_failureSelectedSideTopology {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (htopology : RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G := by
  apply rlc_axisGapPIMSReflectedConfig_mem_event_of_boundaryArc
    G hn hlt tau
  exact rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists
    G hn hlt tau (htopology tau hno)



theorem rlc_axisGapPIMS_success_of_anchoredContourSelector {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (hselector : RlcAxisGapPIMSAnchoredContourSelector G hn hlt)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  rlc_axisGapPIMS_success_of_failureSelectedSideTopology G hn hlt
    (rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector
      G hn hlt hselector) tau hno

end

end StatMech.Universality

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWFailureSelectedCarryObstruction











open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box




structure RlcRetainedFailureAnchoredContour {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) where
  height : ℤ
  firstFace : Site 2
  secondFace : Site 2
  baseFace : Site 2
  contour : (faceBoundaryGraph
    (rlc_mixedWiredReachSet G omega)).Walk baseFace baseFace
  height_lower : G.lower ≤ height
  height_upper : height < G.upper
  axis_inside : ![0, height] ∈ rlc_mixedWiredReachSet G omega
  axis_outside : ![0, height + 1] ∉ rlc_mixedWiredReachSet G omega
  anchor_adj : (faceBoundaryGraph
    (rlc_mixedWiredReachSet G omega)).Adj firstFace secondFace
  anchor_shared : sharedPrimalEdge firstFace secondFace =
    s(![0, height], ![0, height + 1])
  contour_isCycle : contour.IsCycle
  anchor_mem : s(firstFace, secondFace) ∈ contour.edges
  carries_contact_arc :
    RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega contour



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_retainedFailureAnchoredContour
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcRetainedFailureAnchoredContour G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_carriesRelaxedTraceArc
    G hn hlt omega h.contour h.carries_contact_arc




def RlcFailureSelectedExtremalTraceTopology {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Prop :=
  ∀ (omega : ConfigSpace (Sym2 (Site 2))),
    omega ∉ rlc_mixedWiredConnectorEvent G →
      Nonempty (RlcRetainedFailureAnchoredContour G omega)



theorem rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (htopology : RlcFailureSelectedExtremalTraceTopology G)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨h⟩ := htopology omega hno
  exact
    rlc_mixedWiredConnectorEvent_dualReflect_of_retainedFailureAnchoredContour
      G hn hlt omega h



theorem rlc_mixedWiredConnector_half_of_failureSelectedExtremalTraceTopology
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (htopology : RlcFailureSelectedExtremalTraceTopology G) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rlc_mixedWiredConnectorEvent G) := by
  apply rlc_mixedWiredConnector_half_of_dual_reflection G
  intro omega hno
  exact rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology
    G hn hlt htopology omega hno



private theorem rlc_traceSplitCounterexample_fullBoundary_adj01 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![-1, -2] ![-1, -1] := by
  apply (faceBoundaryGraph_adj_vert
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) (-1) (-1) ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj12 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![-1, -1] ![0, -1] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) 0 (-1) ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj23 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![0, -1] ![1, -1] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) 1 (-1) ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj34 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![1, -1] ![1, 0] := by
  apply (faceBoundaryGraph_adj_vert
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) 1 0 ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj45 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![1, 0] ![2, 0] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) 2 0 ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj56 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![2, 0] ![2, -1] := by
  apply faceBoundaryGraph_adj_vert
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj67 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![2, -1] ![2, -2] := by
  apply faceBoundaryGraph_adj_vert
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj78 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![2, -2] ![1, -2] := by
  apply faceBoundaryGraph_adj_horiz
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj89 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![1, -2] ![0, -2] := by
  apply faceBoundaryGraph_adj_horiz
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_fullBoundary_adj90 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![0, -2] ![-1, -2] := by
  apply faceBoundaryGraph_adj_horiz
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp



def rlc_traceSplitCounterexample_fullBoundaryCycle :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Walk
        ![-1, -2] ![-1, -2] :=
  .cons rlc_traceSplitCounterexample_fullBoundary_adj01
    (.cons rlc_traceSplitCounterexample_fullBoundary_adj12
      (.cons rlc_traceSplitCounterexample_fullBoundary_adj23
        (.cons rlc_traceSplitCounterexample_fullBoundary_adj34
          (.cons rlc_traceSplitCounterexample_fullBoundary_adj45
            (.cons rlc_traceSplitCounterexample_fullBoundary_adj56
              (.cons rlc_traceSplitCounterexample_fullBoundary_adj67
                (.cons rlc_traceSplitCounterexample_fullBoundary_adj78
                  (.cons rlc_traceSplitCounterexample_fullBoundary_adj89
                    (.cons rlc_traceSplitCounterexample_fullBoundary_adj90
                      .nil)))))))))

theorem rlc_traceSplitCounterexample_fullBoundaryCycle_isCycle :
    rlc_traceSplitCounterexample_fullBoundaryCycle.IsCycle := by
  rw [rlc_traceSplitCounterexample_fullBoundaryCycle,
    SimpleGraph.Walk.cons_isCycle_iff]
  constructor
  · rw [SimpleGraph.Walk.isPath_def]
    simp
  · simp

theorem rlc_traceSplitCounterexample_fullBoundaryCycle_carriesContactArc :
    RlcFaceBoundaryWalkCarriesRelaxedTraceArc
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig
      rlc_traceSplitCounterexample_fullBoundaryCycle := by
  refine ⟨![-1, -2], ![1, -1],
    rlc_traceSplitCounterexample_boundaryArc
      rlc_windingSideCounterexampleConfig
      rlc_windingSideCounterexample_reachSet_eq, ?_,
    rlc_traceSplitCounterexample_boundaryArc_rightContact,
    rlc_traceSplitCounterexample_boundaryArc_leftContact, ?_⟩
  · intro e he
    rw [rlc_traceSplitCounterexample_boundaryArc_edges] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp [rlc_traceSplitCounterexample_fullBoundaryCycle]
  · exact rlc_traceSplitCounterexample_boundaryArc_relaxed
      rlc_windingSideCounterexampleConfig
      rlc_windingSideCounterexample_reachSet_eq



def rlc_windingSideCounterexample_retainedFailureAnchoredContour :
    RlcRetainedFailureAnchoredContour
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig where
  height := -1
  firstFace := ![-1, -1]
  secondFace := ![0, -1]
  baseFace := ![-1, -2]
  contour := rlc_traceSplitCounterexample_fullBoundaryCycle
  height_lower := by norm_num [rlc_windingSideCounterexampleGap]
  height_upper := by norm_num [rlc_windingSideCounterexampleGap]
  axis_inside := by
    rw [rlc_windingSideCounterexample_reachSet_eq,
      rlc_traceSplitCounterexample_right_vertices]
    simp
  axis_outside := by
    rw [rlc_windingSideCounterexample_reachSet_eq,
      rlc_traceSplitCounterexample_right_vertices]
    simp
  anchor_adj := rlc_traceSplitCounterexample_fullBoundary_adj12
  anchor_shared := by
    simpa using sharedPrimalEdge_right' (-1) (-1)
  contour_isCycle :=
    rlc_traceSplitCounterexample_fullBoundaryCycle_isCycle
  anchor_mem := by
    simp [rlc_traceSplitCounterexample_fullBoundaryCycle]
  carries_contact_arc :=
    rlc_traceSplitCounterexample_fullBoundaryCycle_carriesContactArc



theorem rlc_windingSideCounterexample_dual_success_via_retainedContour :
    rlc_dualReflectConfig rlc_windingSideCounterexampleConfig ∈
      rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
  exact
    rlc_mixedWiredConnectorEvent_dualReflect_of_retainedFailureAnchoredContour
      rlc_windingSideCounterexampleGap (by norm_num)
      (by change (-1 : ℤ) + 1 < 1; omega)
      rlc_windingSideCounterexampleConfig
      rlc_windingSideCounterexample_retainedFailureAnchoredContour

end Universality
end StatMech

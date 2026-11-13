/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWOuterOrientation














open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box



theorem rlc_traceStraddlesLoop_of_endpointSides
    {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d)
    (h : rlc_OppositeLoopSides C
      (gamma.1 : Site 2) (gamma.2.1 : Site 2)) :
    rlc_TraceStraddlesLoop C gamma := by
  refine ⟨gamma.1, ?_, gamma.2.1, ?_, h⟩
  · exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma (gamma.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma).start_mem_support
  · exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma (gamma.2.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma).end_mem_support





theorem rlc_mixedWiredReachSet_separates_traceEndpoints_of_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    (gamma.1.1 : Site 2) ∈ rlc_mixedWiredReachSet G omega ∧
      (gamma.1.2.1 : Site 2) ∈ rlc_mixedWiredReachSet G omega ∧
      (gamma'.1.1 : Site 2) ∉ rlc_mixedWiredReachSet G omega ∧
      (gamma'.1.2.1 : Site 2) ∉ rlc_mixedWiredReachSet G omega := by
  have rightStart : (gamma.1.1 : Site 2) ∈
      rlc_pathVertices gamma.1 :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (gamma.1.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma.1).start_mem_support
  have rightEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma.1 :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (gamma.1.2.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma.1).end_mem_support
  have leftStart : (gamma'.1.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (gamma'.1.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma'.1).start_mem_support
  have leftEnd : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (gamma'.1.2.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma'.1).end_mem_support
  exact ⟨rlc_rightPathVertex_mem_mixedWiredReachSet G omega rightStart,
    rlc_rightPathVertex_mem_mixedWiredReachSet G omega rightEnd,
    rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno leftStart,
    rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno leftEnd⟩




def RlcOuterExitEndpointSides {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  let C := (rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
    (rlc_openSubgraph_le_lattice _)
  rlc_OppositeLoopSides C
      (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2) ∧
    rlc_OppositeLoopSides C
      (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2)



theorem rlc_outerExit_both_straddles_of_endpointSides
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOuterExitEndpointSides G hn hlt omega) :
    rlc_TraceStraddlesLoop
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)) gamma.1 ∧
      rlc_TraceStraddlesLoop
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)) gamma'.1 := by
  exact ⟨rlc_traceStraddlesLoop_of_endpointSides _ gamma.1 h.1,
    rlc_traceStraddlesLoop_of_endpointSides _ gamma'.1 h.2⟩



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitEndpointSides
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hsides : RlcOuterExitEndpointSides G hn hlt omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨hright, hleft⟩ :=
    rlc_outerExit_both_straddles_of_endpointSides G hn hlt omega hsides
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_outerExit_straddles
    G hn hlt omega hright hleft horder




structure RlcOuterExitGoodContactPair {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) where
  rightContact : Site 2
  leftContact : Site 2
  right_mem : rightContact ∈ (mpl_orbitFaceLoop
    (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)).support
  left_mem : leftContact ∈ (mpl_orbitFaceLoop
    (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)).support
  right_trace : rlc_dualReflect rightContact ∈
    rlc_pathVertices gamma.1
  left_trace : rlc_dualReflect leftContact ∈
    rlc_pathVertices gamma'.1
  supportedSide : RlcContourArcRelaxedLocalSide G omega
    (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)) right_mem left_mem




theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitGoodContactPair
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOuterExitGoodContactPair G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide
    G hn hlt omega
    (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega))
    h.right_mem h.left_mem h.right_trace h.left_trace h.supportedSide



def RlcOuterExitGoodContactPair.ofContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (horder : RlcOuterExitContactArcOrder G omega)
    {x y : Site 2}
    (hx : x ∈ (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)).support)
    (hy : y ∈ (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)).support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    RlcOuterExitGoodContactPair G omega where
  rightContact := x
  leftContact := y
  right_mem := hx
  left_mem := hy
  right_trace := hxPath
  left_trace := hyPath
  supportedSide := horder hx hy hxPath hyPath

end Universality
end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWArcBadPlacement
import Code.Lattice.MinimalPeriodLoop



















open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box




structure RlcOrientedContourContactOrder {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) where
  anchor : {e : Dart //
    IsBoundaryDart (rlc_mixedWiredReachSet G omega) e}
  rightContact : Site 2
  leftContact : Site 2
  right_mem : rightContact ∈
    (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) anchor).support
  left_mem : leftContact ∈
    (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) anchor).support
  right_trace : rlc_dualReflect rightContact ∈
    rlc_pathVertices gamma.1
  left_trace : rlc_dualReflect leftContact ∈
    rlc_pathVertices gamma'.1
  supportedSide :
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_orderedContourArc
        (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) anchor)
          right_mem left_mem).edges →
      rlc_contourEdgeRelaxedLocal G f g) ∨
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_complementaryContourArc
        (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) anchor)
          right_mem left_mem).edges →
      rlc_contourEdgeRelaxedLocal G f g)



theorem rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOrientedContourContactOrder G omega) :
    RlcTraceContactsCutOffRelaxedBadEdges G omega
      (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) h.anchor) := by
  let c := mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) h.anchor
  refine ⟨h.rightContact, h.leftContact, h.right_mem, h.left_mem,
    h.right_trace, h.left_trace, ?_⟩
  rcases h.supportedSide with hordered | hcomplementary
  · left
    intro f g hedge hbad
    rcases (rlc_contourArc_edges_cover
      c h.right_mem h.left_mem).mp hedge with hord | hcomp
    · exact False.elim (hbad (hordered hord))
    · exact hcomp
  · right
    intro f g hedge hbad
    rcases (rlc_contourArc_edges_cover
      c h.right_mem h.left_mem).mp hedge with hord | hcomp
    · exact hord
    · exact False.elim (hbad (hcomplementary hcomp))



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerContourContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOrientedContourContactOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide
    G hn hlt omega
    (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) h.anchor)
    h.right_mem h.left_mem h.right_trace h.left_trace h.supportedSide












def rlc_outerExitDart {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (_G : RlcAxisBarrierGap gamma gamma')
    (_omega : ConfigSpace (Sym2 (Site 2))) : Dart :=
  mkDart gamma.1.2.1 (![1, 0] : Site 2) unitWt_px


theorem rlc_outerExitDart_isBoundary {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    IsBoundaryDart (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitDart G omega) := by
  let v : Site 2 := gamma.1.2.1
  have hvPath : v ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨v, by simpa [v] using rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hv : v ∈ rlc_mixedWiredReachSet G omega :=
    rlc_rightPathVertex_mem_mixedWiredReachSet G omega hvPath
  have hvx : v 0 = 2 * n := by
    simpa only [v] using gamma.1.2.1.2.2
  constructor
  · simpa [rlc_outerExitDart, v] using hv
  · intro hhead
    have hbox := rlc_mixedWiredReachSet_subset_box G omega hhead
    rw [mem_rect] at hbox
    have hheadx : (rlc_outerExitDart G omega).head 0 = 2 * n + 1 := by
      simp [rlc_outerExitDart, v, hvx]
    omega


def rlc_outerExitAnchor {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    {e : Dart // IsBoundaryDart (rlc_mixedWiredReachSet G omega) e} :=
  ⟨rlc_outerExitDart G omega, rlc_outerExitDart_isBoundary G omega⟩





theorem rlc_outerExitOrbit_head_reachable {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) (k : ℕ) :
    let K := rlc_mixedWiredReachSet G omega
    let e := rlc_outerExitDart G omega
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨e.head, (rlc_outerExitDart_isBoundary G omega).2⟩
      ⟨((dartNext K)^[k] e).head,
        (iterate_isBoundaryDart' K e
          (rlc_outerExitDart_isBoundary G omega) k).2⟩ := by
  dsimp only
  exact dartNext_orbit_head_sameComponent
    (rlc_mixedWiredReachSet G omega)
    (rlc_outerExitDart G omega)
    ((dartNext (rlc_mixedWiredReachSet G omega))^[k]
      (rlc_outerExitDart G omega))
    (rlc_outerExitDart_isBoundary G omega)
    (iterate_isBoundaryDart'
      (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitDart G omega)
      (rlc_outerExitDart_isBoundary G omega) k)
    rfl



structure RlcOuterContourContactOrder {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) where
  rightContact : Site 2
  leftContact : Site 2
  right_mem : rightContact ∈ (mpl_orbitFaceLoop
    (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)).support
  left_mem : leftContact ∈ (mpl_orbitFaceLoop
    (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)).support
  right_trace : rlc_dualReflect rightContact ∈
    rlc_pathVertices gamma.1
  left_trace : rlc_dualReflect leftContact ∈
    rlc_pathVertices gamma'.1
  supportedSide :
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_orderedContourArc
        (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
          (rlc_outerExitAnchor G omega)) right_mem left_mem).edges →
      rlc_contourEdgeRelaxedLocal G f g) ∨
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_complementaryContourArc
        (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
          (rlc_outerExitAnchor G omega)) right_mem left_mem).edges →
      rlc_contourEdgeRelaxedLocal G f g)


def RlcOuterContourContactOrder.toOriented {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : RlcOuterContourContactOrder G omega) :
    RlcOrientedContourContactOrder G omega where
  anchor := rlc_outerExitAnchor G omega
  rightContact := h.rightContact
  leftContact := h.leftContact
  right_mem := h.right_mem
  left_mem := h.left_mem
  right_trace := h.right_trace
  left_trace := h.left_trace
  supportedSide := h.supportedSide


noncomputable def rlc_outerExitReflectedOpenLoop {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega))).Walk
      (rlc_dualReflect (dartFace (rlc_outerExitAnchor G omega).1))
      (rlc_dualReflect (dartFace (rlc_outerExitAnchor G omega).1)) :=
  rlc_dualReflectOpenWalk
    (rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega)
    ((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)).mapLe
        (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))




def RlcOuterExitContactArcOrder {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∀ {x y : Site 2}
    (hx : x ∈ (mpl_orbitFaceLoop
      (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)).support)
    (hy : y ∈ (mpl_orbitFaceLoop
      (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)).support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
    RlcContourArcRelaxedLocalSide G omega
      (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)) hx hy




theorem rlc_outerExit_traceContactsCutOffRelaxedBadEdges_of_straddles
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hright : rlc_TraceStraddlesLoop
      ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma.1)
    (hleft : rlc_TraceStraddlesLoop
      ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma'.1)
    (horder : RlcOuterExitContactArcOrder G omega) :
    RlcTraceContactsCutOffRelaxedBadEdges G omega
      (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)) := by
  let c := mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
    (rlc_outerExitAnchor G omega)
  let q := rlc_outerExitReflectedOpenLoop G hn hlt omega
  obtain ⟨⟨xr, hxrPath, hxrQ⟩, ⟨yr, hyrPath, hyrQ⟩⟩ :=
    rlc_reflectedOpenDualCycle_contacts_both_of_straddles
      q gamma gamma' hright hleft
  have hqSupport : q.support = List.map rlc_dualReflect c.support := by
    simp [q, c, rlc_outerExitReflectedOpenLoop,
      rlc_dualReflectOpenWalk, SimpleGraph.Walk.support_map,
      SimpleGraph.Walk.support_mapLe_eq_support, rlc_dualReflectOpenHom]
  rw [hqSupport] at hxrQ hyrQ
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hxrQ
  obtain ⟨y, hy, hyr⟩ := List.mem_map.mp hyrQ
  have hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
    simpa using hxr ▸ hxrPath
  have hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
    simpa using hyr ▸ hyrPath
  let hdata : RlcOuterContourContactOrder G omega := {
    rightContact := x
    leftContact := y
    right_mem := hx
    left_mem := hy
    right_trace := hxPath
    left_trace := hyPath
    supportedSide := horder hx hy hxPath hyPath }
  exact rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder
    G omega hdata.toOriented



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerExit_straddles
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hright : rlc_TraceStraddlesLoop
      ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma.1)
    (hleft : rlc_TraceStraddlesLoop
      ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma'.1)
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, y, hx, hy, hxPath, hyPath, _hplace⟩ :=
    rlc_outerExit_traceContactsCutOffRelaxedBadEdges_of_straddles
      G hn hlt omega hright hleft horder
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide
    G hn hlt omega
    (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega))
    hx hy hxPath hyPath (horder hx hy hxPath hyPath)



theorem rlc_traceContactsCutOffRelaxedBadEdges_of_outerExitContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOuterContourContactOrder G omega) :
    RlcTraceContactsCutOffRelaxedBadEdges G omega
      (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)) :=
  rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder
    G omega h.toOriented



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOuterContourContactOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G :=
  rlc_mixedWiredConnectorEvent_dualReflect_of_outerContourContactOrder
    G hn hlt omega h.toOriented

end Universality
end StatMech

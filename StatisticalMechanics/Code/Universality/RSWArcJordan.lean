/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWOuterArc
import Code.Universality.RSWTraceContact
















open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box




theorem rlc_reflectedTargetLocallySupported_endpoint_mem_connectorBox
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : rlc_reflectedTargetLocallySupported G e)
    {z : Site 2} (hz : z ∈ e) : z ∈ rlc_connectorBox n := by
  rcases he with hexposed | hgap | hright | hleft
  · induction e using Sym2.inductionOn with
    | _ x y =>
        rw [Sym2.mem_iff] at hz
        have hends := rlc_exposedPathEdges_endpoints_mem_box hexposed
        rcases hz with rfl | rfl
        · simpa [rlc_connectorBox] using hends.1
        · simpa [rlc_connectorBox] using hends.2
  · have hzFlip : rlc_flipX z ∈ e.map rlc_flipX := by
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp only [Sym2.map_mk]
          rw [Sym2.mem_iff] at hz ⊢
          rcases hz with rfl | rfl <;> simp
    have hzRect : rlc_flipX z ∈
        rect (-2 * n) (2 * n) (-n) n := hgap.1 _ hzFlip
    have : z ∈ rect (-2 * n) (2 * n) (-n) n :=
      (rlc_mem_connectorBox_flipX z).mpr hzRect
    simpa [rlc_connectorBox] using this
  · have hzRect :=
      rlc_reflectedRightPathEdge_endpoint_mem_box gamma hright hz
    simpa [rlc_connectorBox] using hzRect
  · have hzRect :=
      rlc_reflectedLeftPathEdge_endpoint_mem_box gamma' hleft hz
    simpa [rlc_connectorBox] using hzRect



theorem rlc_walk_support_mem_connectorBox_of_targetLocal
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {x y : Site 2}
    {H : SimpleGraph (Site 2)} (a : H.Walk x y)
    (hy : y ∈ rlc_connectorBox n)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_reflectedTargetLocallySupported G s(f, g)) :
    ∀ z ∈ a.support, z ∈ rlc_connectorBox n := by
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact hy
  · induction e using Sym2.inductionOn with
    | _ f g =>
        exact rlc_reflectedTargetLocallySupported_endpoint_mem_connectorBox
          G (hlocal he) hze



theorem rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {x y : Site 2}
    {H : SimpleGraph (Site 2)} (a : H.Walk x y)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g)) :
    ∀ z ∈ a.support,
      rlc_dualReflect z ∈ rlc_connectorBox n := by
  have hyBox : rlc_dualReflect y ∈ rlc_connectorBox n := by
    simpa [rlc_connectorBox] using
      rlc_leftPathVertex_mem_connectorBox gamma' hyPath
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact hyBox
  · induction e using Sym2.inductionOn with
    | _ f g =>
        apply rlc_reflectedTargetLocallySupported_endpoint_mem_connectorBox
          G (hlocal he)
        rw [Sym2.mem_iff] at hze ⊢
        rcases hze with rfl | rfl <;> simp



def RlcContourArcLocalSide {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : Prop :=
  (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges →
      rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) ∨
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_complementaryContourArc c hx hy).edges →
      rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g))




theorem rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcLocalSide
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hside : RlcContourArcLocalSide G omega c hx hy) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  apply rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcSide
    G hn hlt omega c hx hy hxPath hyPath
  rcases hside with hforward | hbackward
  · left
    refine ⟨?_, hforward⟩
    exact rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal
      G (rlc_orderedContourArc c hx hy) hyPath (fun he => (hforward he).1)
  · right
    refine ⟨?_, hbackward⟩
    exact rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal
      G (rlc_complementaryContourArc c hx hy) hyPath
        (fun he => (hbackward he).1)





theorem rlc_mixedWiredConnectorEvent_dualReflect_of_straddles_of_arcLocalSide
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hright : rlc_TraceStraddlesLoop
      ((rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma.1)
    (hleft : rlc_TraceStraddlesLoop
      ((rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma'.1)
    (hJordan : ∀ {x y : Site 2}
      (hx : x ∈ c.support) (hy : y ∈ c.support),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
      RlcContourArcLocalSide G omega c hx hy) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega
  let q := rlc_dualReflectOpenWalk eta (c.mapLe hle)
  obtain ⟨⟨xr, hxrPath, hxrQ⟩, ⟨yr, hyrPath, hyrQ⟩⟩ :=
    rlc_reflectedOpenDualCycle_contacts_both_of_straddles
      q gamma gamma' hright hleft
  have hqSupport : q.support = List.map rlc_dualReflect c.support := by
    simp [q, rlc_dualReflectOpenWalk, SimpleGraph.Walk.support_map,
      SimpleGraph.Walk.support_mapLe_eq_support, rlc_dualReflectOpenHom]
  rw [hqSupport] at hxrQ hyrQ
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hxrQ
  obtain ⟨y, hy, hyr⟩ := List.mem_map.mp hyrQ
  have hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
    simpa using hxr ▸ hxrPath
  have hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
    simpa using hyr ▸ hyrPath
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcLocalSide
    G hn hlt omega c hx hy hxPath hyPath
      (hJordan hx hy hxPath hyPath)

end Universality
end StatMech

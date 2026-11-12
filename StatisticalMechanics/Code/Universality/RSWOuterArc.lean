/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWArcSupport
import Code.Universality.RSWGapSymmetry















open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box



noncomputable def rlc_orderedContourArc {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : H.Walk x y :=
  (c.rotate x hx).takeUntil y
    ((SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy)



noncomputable def rlc_complementaryContourArc {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : H.Walk x y :=
  ((c.rotate x hx).dropUntil y
    ((SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy)).reverse



theorem rlc_orderedContourArc_support_subset {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (rlc_orderedContourArc c hx hy).support ⊆ c.support := by
  intro z hz
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have hzrot : z ∈ (c.rotate x hx).support :=
    (c.rotate x hx).support_takeUntil_subset_support hy' hz
  exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).1 hzrot


theorem rlc_orderedContourArc_edges_subset {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (rlc_orderedContourArc c hx hy).edges ⊆ c.edges := by
  intro e he
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have herot : e ∈ (c.rotate x hx).edges :=
    (c.rotate x hx).edges_takeUntil_subset hy' he
  exact (SimpleGraph.Walk.rotate_edges c x hx).perm.mem_iff.mp herot



theorem rlc_complementaryContourArc_support_subset
    {H : SimpleGraph (Site 2)} {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (rlc_complementaryContourArc c hx hy).support ⊆ c.support := by
  intro z hz
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have hzdrop : z ∈ ((c.rotate x hx).dropUntil y hy').support := by
    simpa [rlc_complementaryContourArc,
      SimpleGraph.Walk.support_reverse] using hz
  have hzrot : z ∈ (c.rotate x hx).support :=
    (c.rotate x hx).support_dropUntil_subset hy' hzdrop
  exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).1 hzrot



theorem rlc_complementaryContourArc_edges_subset
    {H : SimpleGraph (Site 2)} {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (rlc_complementaryContourArc c hx hy).edges ⊆ c.edges := by
  intro e he
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have hedrop : e ∈ ((c.rotate x hx).dropUntil y hy').edges := by
    simpa [rlc_complementaryContourArc,
      SimpleGraph.Walk.edges_reverse] using he
  have herot : e ∈ (c.rotate x hx).edges :=
    (c.rotate x hx).edges_dropUntil_subset hy' hedrop
  exact (SimpleGraph.Walk.rotate_edges c x hx).perm.mem_iff.mp herot





theorem rlc_select_complementaryContourArc {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (Pv : Site 2 → Prop) (Pe : Sym2 (Site 2) → Prop)
    (hside :
      ((∀ z ∈ (rlc_orderedContourArc c hx hy).support, Pv z) ∧
        (∀ e ∈ (rlc_orderedContourArc c hx hy).edges, Pe e)) ∨
      ((∀ z ∈ (rlc_complementaryContourArc c hx hy).support, Pv z) ∧
        (∀ e ∈ (rlc_complementaryContourArc c hx hy).edges, Pe e))) :
    ∃ a : H.Walk x y,
      (∀ z ∈ a.support, Pv z) ∧
      (∀ e ∈ a.edges, Pe e) ∧
      a.support ⊆ c.support ∧ a.edges ⊆ c.edges := by
  rcases hside with hforward | hbackward
  · exact ⟨rlc_orderedContourArc c hx hy, hforward.1, hforward.2,
      rlc_orderedContourArc_support_subset c hx hy,
      rlc_orderedContourArc_edges_subset c hx hy⟩
  · exact ⟨rlc_complementaryContourArc c hx hy, hbackward.1, hbackward.2,
      rlc_complementaryContourArc_support_subset c hx hy,
      rlc_complementaryContourArc_edges_subset c hx hy⟩



theorem rlc_orderedContourArc_vertex_property {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (P : Site 2 → Prop) (hP : ∀ z ∈ c.support, P z) :
    ∀ z ∈ (rlc_orderedContourArc c hx hy).support, P z := by
  intro z hz
  exact hP z (rlc_orderedContourArc_support_subset c hx hy hz)



theorem rlc_orderedContourArc_edge_property {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (P : Sym2 (Site 2) → Prop) (hP : ∀ e ∈ c.edges, P e) :
    ∀ e ∈ (rlc_orderedContourArc c hx hy).edges, P e := by
  intro e he
  exact hP e (rlc_orderedContourArc_edges_subset c hx hy he)




theorem rlc_faceBoundaryWalk_reflected_support_mem_connectorBox
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hbox : ∀ z ∈ a.support,
      rlc_dualReflect z ∈ rlc_connectorBox n) :
    ∀ z ∈ (rlc_dualReflectOpenWalk
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega)
      (a.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
        G hn hlt omega))).support,
      z ∈ rlc_connectorBox n := by
  intro z hz
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
    G hn hlt omega
  have hzmap : z ∈ List.map (rlc_dualReflectOpenHom eta)
      (a.mapLe hle).support := by
    change z ∈ ((a.mapLe hle).map
      (rlc_dualReflectOpenHom eta)).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    exact hz
  obtain ⟨w, hw, hwz⟩ := List.mem_map.mp hzmap
  change rlc_dualReflect w = z at hwz
  subst z
  apply hbox w
  simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hw



theorem rlc_orderedFaceBoundaryArc_reflected_support_mem_connectorBox
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hbox : ∀ z ∈ c.support,
      rlc_dualReflect z ∈ rlc_connectorBox n) :
    ∀ z ∈ (rlc_dualReflectOpenWalk
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega)
      ((rlc_orderedContourArc c hx hy).mapLe
        (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).support,
      z ∈ rlc_connectorBox n := by
  apply rlc_faceBoundaryWalk_reflected_support_mem_connectorBox
    G hn hlt omega (rlc_orderedContourArc c hx hy)
  intro z hz
  exact hbox z (rlc_orderedContourArc_support_subset c hx hy hz)





theorem rlc_mixedWiredConnectorEvent_dualReflect_of_orderedContourContacts
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
    (hbox : ∀ z ∈ c.support,
      rlc_dualReflect z ∈ rlc_connectorBox n)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  let a := rlc_orderedContourArc c hx hy
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
    G hn hlt omega
  obtain ⟨q, _hqEdges, hqSupport⟩ :=
    rlc_dualReflect_wired_faceBoundaryWalk_of_local_support
      G hn hlt omega a (by
        intro f g hfg
        exact hlocal (rlc_orderedContourArc_edges_subset c hx hy hfg))
  apply rlc_mixedWiredConnectorEvent_of_openWalk_meets_paths
    G (rlc_dualReflectConfig omega) q
  · intro z hz
    apply rlc_orderedFaceBoundaryArc_reflected_support_mem_connectorBox
      G hn hlt omega c hx hy hbox z
    simpa [a, eta, hle, hqSupport] using hz
  · refine ⟨rlc_dualReflect x, ?_, hxPath⟩
    have hxq : rlc_dualReflect x ∈ q.support := by
      rw [hqSupport]
      exact (rlc_dualReflectOpenWalk eta (a.mapLe hle)).start_mem_support
    exact hxq
  · refine ⟨rlc_dualReflect y, ?_, hyPath⟩
    have hyq : rlc_dualReflect y ∈ q.support := by
      rw [hqSupport]
      exact (rlc_dualReflectOpenWalk eta (a.mapLe hle)).end_mem_support
    exact hyq





theorem rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcSide
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
    (hside :
      ((∀ z ∈ (rlc_orderedContourArc c hx hy).support,
          rlc_dualReflect z ∈ rlc_connectorBox n) ∧
        (∀ {f g : Site 2},
          s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges →
          rlc_reflectedTargetLocallySupported G
              s(rlc_dualReflect f, rlc_dualReflect g) ∧
            rlc_boundarySourceLocallySupported G
              (sharedPrimalEdge f g))) ∨
      ((∀ z ∈ (rlc_complementaryContourArc c hx hy).support,
          rlc_dualReflect z ∈ rlc_connectorBox n) ∧
        (∀ {f g : Site 2},
          s(f, g) ∈ (rlc_complementaryContourArc c hx hy).edges →
          rlc_reflectedTargetLocallySupported G
              s(rlc_dualReflect f, rlc_dualReflect g) ∧
            rlc_boundarySourceLocallySupported G
              (sharedPrimalEdge f g)))) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨a, haBox, haLocal⟩ :
      ∃ a : (faceBoundaryGraph
          (rlc_mixedWiredReachSet G omega)).Walk x y,
        (∀ z ∈ a.support,
          rlc_dualReflect z ∈ rlc_connectorBox n) ∧
        (∀ {f g : Site 2}, s(f, g) ∈ a.edges →
          rlc_reflectedTargetLocallySupported G
              s(rlc_dualReflect f, rlc_dualReflect g) ∧
            rlc_boundarySourceLocallySupported G
              (sharedPrimalEdge f g)) := by
    rcases hside with hforward | hbackward
    · exact ⟨rlc_orderedContourArc c hx hy,
        hforward.1, hforward.2⟩
    · exact ⟨rlc_complementaryContourArc c hx hy,
        hbackward.1, hbackward.2⟩
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
    G hn hlt omega
  obtain ⟨q, _hqEdges, hqSupport⟩ :=
    rlc_dualReflect_wired_faceBoundaryWalk_of_local_support
      G hn hlt omega a (by
        intro f g hfg
        exact haLocal hfg)
  apply rlc_mixedWiredConnectorEvent_of_openWalk_meets_paths
    G (rlc_dualReflectConfig omega) q
  · intro z hz
    apply rlc_faceBoundaryWalk_reflected_support_mem_connectorBox
      G hn hlt omega a haBox z
    simpa [eta, hle, hqSupport] using hz
  · refine ⟨rlc_dualReflect x, ?_, hxPath⟩
    rw [hqSupport]
    exact (rlc_dualReflectOpenWalk eta (a.mapLe hle)).start_mem_support
  · refine ⟨rlc_dualReflect y, ?_, hyPath⟩
    rw [hqSupport]
    exact (rlc_dualReflectOpenWalk eta (a.mapLe hle)).end_mem_support

end Universality
end StatMech

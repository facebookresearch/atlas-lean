/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWLowestCrossing

open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech

namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box

@[simp] theorem rlc_flipX_mem_image_iff (P : Finset (Site 2))
    (z : Site 2) :
    rlc_flipX z ∈ P.image rlc_flipX ↔ z ∈ P := by
  classical
  constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_image.mp hz
    have hwz : w = z := rlc_flipX.injective hzw
    simpa [hwz] using hw
  · intro hz
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

@[simp] theorem rlc_mem_flipX_image_iff (P : Finset (Site 2))
    (z : Site 2) :
    z ∈ P.image rlc_flipX ↔ rlc_flipX z ∈ P := by
  simpa using rlc_flipX_mem_image_iff P (rlc_flipX z)

theorem rlc_connectorBarrier_mem_flipX_iff {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) :
    z ∈ rlc_connectorBarrier gamma gamma' ↔
      rlc_flipX z ∈ rlc_connectorBarrier gamma gamma' := by
  classical
  simp only [rlc_connectorBarrier, Finset.mem_union,
    rlc_mem_flipX_image_iff, rlc_flipX_involutive]
  tauto

theorem rlc_connectorBox_mem_flipX_iff {n : ℤ} (z : Site 2) :
    z ∈ rlc_connectorBox n ↔ rlc_flipX z ∈ rlc_connectorBox n := by
  simpa [rlc_connectorBox] using rlc_mem_connectorBox_flipX (n := n) z

theorem rlc_connectorAllowed_mem_flipX_iff {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) :
    z ∈ rlc_connectorAllowed gamma gamma' ↔
      rlc_flipX z ∈ rlc_connectorAllowed gamma gamma' := by
  simp only [rlc_connectorAllowed, Finset.mem_sdiff]
  rw [
    rlc_connectorBox_mem_flipX_iff,
    rlc_connectorBarrier_mem_flipX_iff]

theorem rlc_adj_flipX (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_flipX x) (rlc_flipX y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rlc_flipX, rlc_flipXFun, Equiv.coe_fn_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (-x 0) - (-y 0) = -(x 0 - y 0) by ring, Int.natAbs_neg]

private noncomputable def rlc_axisGapFlipHom {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (_G : RlcAxisBarrierGap gamma gamma') :
    ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))) →g
    ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))) where
  toFun x := ⟨rlc_flipX x,
    (rlc_connectorAllowed_mem_flipX_iff gamma gamma' x).mp x.2⟩
  map_rel' := by
    intro x y hxy
    rw [SimpleGraph.induce_adj] at hxy ⊢
    exact (rlc_adj_flipX x y).mp hxy

theorem rlc_axisGapRegionSet_mem_flipX {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {z : Site 2}
    (hz : z ∈ rlc_axisGapRegionSet G) :
    rlc_flipX z ∈ rlc_axisGapRegionSet G := by
  obtain ⟨hzAllowed, hsAllowed, hreach⟩ := hz
  have hzAllowed' : rlc_flipX z ∈ rlc_connectorAllowed gamma gamma' :=
    (rlc_connectorAllowed_mem_flipX_iff gamma gamma' z).mp hzAllowed
  have hreach' := hreach.map (rlc_axisGapFlipHom G)
  refine ⟨hzAllowed', hsAllowed, ?_⟩
  simpa [rlc_axisGapFlipHom, RlcAxisBarrierGap.seedVertex,
    rlc_flipX, rlc_flipXFun] using hreach'

theorem rlc_axisGapRegionSet_mem_flipX_iff {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (z : Site 2) :
    z ∈ rlc_axisGapRegionSet G ↔
      rlc_flipX z ∈ rlc_axisGapRegionSet G := by
  constructor
  · exact rlc_axisGapRegionSet_mem_flipX G
  · intro hz
    simpa using rlc_axisGapRegionSet_mem_flipX G hz

theorem rlc_axisGapRegion_mem_flipX_iff {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (z : Site 2) :
    z ∈ rlc_axisGapRegion G ↔ rlc_flipX z ∈ rlc_axisGapRegion G := by
  simpa [rlc_axisGapRegion] using rlc_axisGapRegionSet_mem_flipX_iff G z

@[simp] theorem RlcAxisBarrierGap.firstEdge_map_flipX {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.firstEdge.map rlc_flipX = G.firstEdge := by
  simp [RlcAxisBarrierGap.firstEdge, RlcAxisBarrierGap.lowerVertex,
    RlcAxisBarrierGap.seedVertex, Sym2.map_mk, rlc_flipX,
    rlc_flipXFun]

@[simp] theorem rlc_edge_map_flipX_involutive (e : Sym2 (Site 2)) :
    (e.map rlc_flipX).map rlc_flipX = e := by
  induction e using Sym2.inductionOn with
  | _ x y => simp [Sym2.map_mk]

theorem rlc_axisGapEdges_mem_map_flipX {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G) :
    e.map rlc_flipX ∈ rlc_axisGapEdges G := by
  rw [rlc_axisGapEdges, Finset.mem_union] at he ⊢
  rcases he with he | he
  · left
    rw [Finset.mem_filter] at he ⊢
    refine ⟨?_, ?_⟩
    · rw [mem_edgesWithinFinset] at he ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := he.1
      exact ⟨rlc_flipX x, (rlc_connectorBox_mem_flipX_iff x).mp hx,
        rlc_flipX y, (rlc_connectorBox_mem_flipX_iff y).mp hy,
        by simp [Sym2.map_mk]⟩
    · obtain ⟨z, hzRegion, hzEdge⟩ := he.2
      refine ⟨rlc_flipX z,
        (rlc_axisGapRegion_mem_flipX_iff G z).mp hzRegion, ?_⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp only [Sym2.map_mk]
          rw [Sym2.mem_iff] at hzEdge ⊢
          rcases hzEdge with rfl | rfl <;> simp
  · right
    rw [Finset.mem_singleton] at he ⊢
    rw [he, G.firstEdge_map_flipX]

theorem rlc_axisGapEdges_mem_map_flipX_iff {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) :
    e ∈ rlc_axisGapEdges G ↔ e.map rlc_flipX ∈ rlc_axisGapEdges G := by
  constructor
  · exact rlc_axisGapEdges_mem_map_flipX G
  · intro he
    simpa using rlc_axisGapEdges_mem_map_flipX G he






def rlc_edgeBoxIncidentGap {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) : Prop :=
  (∀ z ∈ e, z ∈ rect (-2 * n) (2 * n) (-n) n) ∧
    ∃ z ∈ rlc_axisGapRegion G, z ∈ e



theorem rlc_mem_axisGapEdges_of_edgeBoxIncidentGap {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : rlc_edgeBoxIncidentGap G e) :
    e ∈ rlc_axisGapEdges G := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  refine ⟨?_, he.2⟩
  rw [mem_edgesWithinFinset]
  induction e using Sym2.inductionOn with
  | _ v w =>
      have hv : v ∈ rlc_connectorBox n := by
        simpa [rlc_connectorBox] using
          he.1 v (Sym2.mem_mk_left v w)
      have hw : w ∈ rlc_connectorBox n := by
        simpa [rlc_connectorBox] using
          he.1 w (Sym2.mem_mk_right v w)
      exact ⟨v, hv, w, hw, rfl⟩



theorem rlc_mem_axisGapEdges_of_flipX_edgeBoxIncidentGap {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : rlc_edgeBoxIncidentGap G (e.map rlc_flipX)) :
    e ∈ rlc_axisGapEdges G := by
  exact (rlc_axisGapEdges_mem_map_flipX_iff G e).mpr
    (rlc_mem_axisGapEdges_of_edgeBoxIncidentGap G he)




theorem rlc_mem_exposed_union_mixedAxisGapEdges_iff {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) :
    e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
        rlc_mixedAxisGapEdges G ↔
      e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
      e ∈ rlc_axisGapEdges G ∨
      e ∈ rlc_reflectedPathEdges gamma.1 ∨
      e ∈ rlc_reflectedPathEdges gamma'.1 := by
  simp only [rlc_mixedAxisGapEdges, Finset.mem_union, Finset.mem_sdiff]
  tauto



theorem rlc_axisGapEdge_mem_exposed_union_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G) :
    e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
      rlc_mixedAxisGapEdges G := by
  rw [rlc_mem_exposed_union_mixedAxisGapEdges_iff G e]
  exact Or.inr (Or.inl he)


theorem rlc_axisGapEdge_mem_mixedAxisGapEdges_of_not_exposed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G)
    (hnot : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    e ∈ rlc_mixedAxisGapEdges G := by
  rw [rlc_mixedAxisGapEdges, Finset.mem_sdiff]
  exact ⟨by simp [he], hnot⟩



theorem rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (S : Set (Site 2)) {f g : Site 2}
    (hfg : (faceBoundaryGraph S).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) =
      sharedPrimalEdge f g := by
  exact rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg.1



theorem rlc_gapSymmetry_faceBoundary_preimage_not_exposed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  intro hexposed
  rw [rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (rlc_mixedWiredReachSet G omega) hfg] at hexposed
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈
      edgeBoundary 2 (rlc_mixedWiredReachSet G omega) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_mixedWiredReachSet_edgeBoundary_closed
    G hn hlt omega hpqBoundary
  have hopen : rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega (sharedPrimalEdge f g) = true := by
    simp [rlc_wiredConnectorConfig, hexposed]
  rw [hpq] at hopen
  rw [hopen] at hclosed
  simp at hclosed




theorem rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_mixedAxisGapEdges G ↔
      sharedPrimalEdge f g ∈ rlc_axisGapEdges G ∨
      sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma.1 ∨
      sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma'.1 := by
  have hpims := rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (rlc_mixedWiredReachSet G omega) hfg
  have hnot : sharedPrimalEdge f g ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    rw [← hpims]
    exact rlc_gapSymmetry_faceBoundary_preimage_not_exposed
      G hn hlt omega hfg
  rw [hpims]
  simp only [rlc_mixedAxisGapEdges, Finset.mem_sdiff, Finset.mem_union]
  have hnot' : ¬(sharedPrimalEdge f g ∈ rlc_pathEdges gamma.1 ∨
      sharedPrimalEdge f g ∈ rlc_pathEdges gamma'.1) := by
    simpa only [Finset.mem_union] using hnot
  constructor
  · rintro ⟨hsupport, _⟩
    rcases hsupport with (hgap | hright) | hleft
    · exact Or.inl hgap
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr hleft)
  · intro hsupport
    refine ⟨?_, hnot'⟩
    rcases hsupport with hgap | hright | hleft
    · exact Or.inl (Or.inl hgap)
    · exact Or.inl (Or.inr hright)
    · exact Or.inr hleft




def rlc_reflectedTargetLocallySupported {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) : Prop :=
  e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
    rlc_edgeBoxIncidentGap G (e.map rlc_flipX) ∨
    e ∈ rlc_reflectedPathEdges gamma.1 ∨
    e ∈ rlc_reflectedPathEdges gamma'.1




def rlc_boundarySourceLocallySupported {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) : Prop :=
  rlc_edgeBoxIncidentGap G e ∨
    e ∈ rlc_reflectedPathEdges gamma.1 ∨
    e ∈ rlc_reflectedPathEdges gamma'.1





theorem rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g)
    (htarget : rlc_reflectedTargetLocallySupported G
      s(rlc_dualReflect f, rlc_dualReflect g))
    (hsource : rlc_boundarySourceLocallySupported G
      (sharedPrimalEdge f g)) :
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
        (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
          rlc_mixedAxisGapEdges G ∧
      rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_mixedAxisGapEdges G := by
  constructor
  · rw [rlc_mem_exposed_union_mixedAxisGapEdges_iff G]
    rcases htarget with hexposed | hgap | hright | hleft
    · exact Or.inl hexposed
    · exact Or.inr (Or.inl
        (rlc_mem_axisGapEdges_of_flipX_edgeBoxIncidentGap G hgap))
    · exact Or.inr (Or.inr (Or.inl hright))
    · exact Or.inr (Or.inr (Or.inr hleft))
  · rw [rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff
      G hn hlt omega hfg]
    rcases hsource with hgap | hright | hleft
    · exact Or.inl (rlc_mem_axisGapEdges_of_edgeBoxIncidentGap G hgap)
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr hleft)




theorem rlc_dualReflect_wired_faceBoundaryWalk_of_local_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) :
    ∃ q : (openSubgraph 2
      (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
        (rlc_dualReflectConfig omega))).Walk
        (rlc_dualReflect x) (rlc_dualReflect y),
      q.edges = (rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).edges ∧
      q.support = (rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).support := by
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
    G hn hlt omega
  let p := rlc_dualReflectOpenWalk eta (c.mapLe hle)
  apply rlc_dualReflect_wired_walk_of_support G omega p
  intro e he
  have hEdges : p.edges =
      (c.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (c.mapLe hle)
  rw [hEdges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  induction e0 using Sym2.inductionOn with
  | _ f g =>
      have hfgEdge : s(f, g) ∈ c.edges := by
        rw [c.edges_mapLe_eq_edges hle] at he0
        exact he0
      exact rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local
        G hn hlt omega (c.adj_of_mem_edges hfgEdge)
          (hlocal hfgEdge).1 (hlocal hfgEdge).2

end Universality

end StatMech

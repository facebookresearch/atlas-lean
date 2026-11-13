/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickInnerFaces
import Code.FK.TriangularSharpness
import Code.FK.OffCentreDomination









open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls

noncomputable section


def triHexBrickInnerBoundary (N : Nat)
    (x : {z : Site 2 // z ∈ box 2 N}) : Prop :=
  x ∈ triangularBoxShell N N

noncomputable instance triHexBrickInnerBoundaryDecidable (N : Nat) :
    DecidablePred (triHexBrickInnerBoundary N) := Classical.decPred _



theorem triHexBrickInnerFaceMap_adjMatch
    {N m : Nat} (hNm : N < m) :
    ocd_AdjMatch (triHexBrickInnerTriangleGraph N)
      (triHexBrickFullDualGraph m) (triHexBrickInnerFaceMap N m) :=
  triHexBrickInnerFaceMap_adj hNm



theorem triHexBrickInner_boundary_of_outsideGraph_adj
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    (psi : ConfigSpace
      (Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))))
    {x : {z : Site 2 // z ∈ box 2 N}}
    {C : kwg_Face (triHexPlanarFiniteStarPlanar m)}
    (h : (ocd_outsideGraph (triHexBrickFullDualGraph m)
      (triHexBrickInnerFaceMap N m) (fun _ => False) psi).Adj
        (triHexBrickInnerFaceMap N m x) C) :
    triHexBrickInnerBoundary N x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hxfalse, _⟩
  · simp only [triHexBrickInnerBoundary, triangularBoxShell,
      Finset.mem_filter, Finset.mem_univ, true_and, mem_vertexBoundary]
    refine ⟨x.2, ?_⟩
    intro hxinner
    rw [triHexBrickFullDualGraph, BeffaraDC.pfdClosedDual_adj] at hadj
    obtain ⟨_, e, _, hends⟩ := hadj
    generalize ha : (triHexPlanarFiniteStarEdgeEquiv m).symm e = a
    rcases a with ⟨z, i⟩
    have he := (triHexPlanarFiniteStarEdgeEquiv m).apply_symm_apply e
    rw [ha] at he
    rw [← he, triHexPlanarFiniteStar_dualEnds] at hends
    rw [Sym2.eq_iff] at hends
    rcases hends with hends | hends
    · have hx : triHexSpokeFace1 z.1 i = x.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp hends.1
      have hxy : triangularGraph.Adj x.1 (triHexSpokeFace2 z.1 i) := by
        simpa [hx] using triHexSpokeFaces_adj z.1 i
      have hy : triHexSpokeFace2 z.1 i ∈ box 2 N :=
        triangular_adj_mem_box_of_mem_pred hN hxinner hxy
      let y : {w : Site 2 // w ∈ box 2 N} :=
        ⟨triHexSpokeFace2 z.1 i, hy⟩
      have hC : triHexBrickInnerFaceMap N m y = C := by
        simpa [triHexBrickInnerFaceMap, y] using hends.2
      apply hrange
      refine ⟨s(x, y), ?_⟩
      rw [ocd_innerEdge_mk, hC]
    · have hx : triHexSpokeFace2 z.1 i = x.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp hends.2
      have hxy : triangularGraph.Adj x.1 (triHexSpokeFace1 z.1 i) := by
        simpa [hx] using (triHexSpokeFaces_adj z.1 i).symm
      have hy : triHexSpokeFace1 z.1 i ∈ box 2 N :=
        triangular_adj_mem_box_of_mem_pred hN hxinner hxy
      let y : {w : Site 2 // w ∈ box 2 N} :=
        ⟨triHexSpokeFace1 z.1 i, hy⟩
      have hC : triHexBrickInnerFaceMap N m y = C := by
        simpa [triHexBrickInnerFaceMap, y] using hends.1
      apply hrange
      refine ⟨s(x, y), ?_⟩
      rw [ocd_innerEdge_mk, hC]
  · exact hxfalse.elim



theorem triHexBrickInner_inducedWiring_le_boundaryClique
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    (psi : ConfigSpace
      (Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m)))) :
    ocd_inducedWiring (triHexBrickFullDualGraph m)
        (triHexBrickInnerFaceMap N m) (fun _ => False) psi ≤
      boundaryCliqueGraph (triHexBrickInnerBoundary N) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexBrickInnerFaceMap N m x ≠
        triHexBrickInnerFaceMap N m y :=
      fun heq => hne (triHexBrickInnerFaceMap_injective hNm heq)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact triHexBrickInner_boundary_of_outsideGraph_adj
        hNm hN psi hadj
  · have hreach' :
        (ocd_outsideGraph (triHexBrickFullDualGraph m)
          (triHexBrickInnerFaceMap N m) (fun _ => False) psi).Reachable
            (triHexBrickInnerFaceMap N m y)
            (triHexBrickInnerFaceMap N m x) := hreach.symm
    have hne' : triHexBrickInnerFaceMap N m y ≠
        triHexBrickInnerFaceMap N m x :=
      fun heq => hne (triHexBrickInnerFaceMap_injective hNm heq).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact triHexBrickInner_boundary_of_outsideGraph_adj
        hNm hN psi hadj

end

end StatMech.FK.PeriodicPlanar

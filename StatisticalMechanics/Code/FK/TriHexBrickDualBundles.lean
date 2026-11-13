/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickDominationGeometry
import Code.FrontierD.FKQgt4SquareDualBundles









open Finset Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls
open StatMech.FrontierD

noncomputable section



theorem triHexSpokeFaces_eq_triangularIndexedEdge
    (z : Site 2) (i : Fin 3) :
    s(triHexSpokeFace1 z i, triHexSpokeFace2 z i) =
      triangularIndexedEdge (triHexIndexEquiv.symm (z, i)) := by
  fin_cases i <;>
    simp [triHexSpokeFace1, triHexSpokeFace2, triHexIndexEquiv,
      triangularIndexedEdge, triangularStep, hexagonalStep]



theorem triHexBrick_edge_eq_of_dualEnds_eq_inner
    {N m : Nat} (hNm : N < m)
    {x y : {z : Site 2 // z ∈ box 2 N}}
    {e f : kwg_Edge (triHexPlanarFiniteStarPlanar m)}
    (he : kwg_dualEnds (triHexPlanarFiniteStarPlanar m) e =
      s(triHexBrickInnerFaceMap N m x,
        triHexBrickInnerFaceMap N m y))
    (hf : kwg_dualEnds (triHexPlanarFiniteStarPlanar m) f =
      s(triHexBrickInnerFaceMap N m x,
        triHexBrickInnerFaceMap N m y)) :
    e = f := by
  generalize hae : (triHexPlanarFiniteStarEdgeEquiv m).symm e = a
  generalize haf : (triHexPlanarFiniteStarEdgeEquiv m).symm f = b
  rcases a with ⟨z, i⟩
  rcases b with ⟨w, j⟩
  have hae' := (triHexPlanarFiniteStarEdgeEquiv m).apply_symm_apply e
  have haf' := (triHexPlanarFiniteStarEdgeEquiv m).apply_symm_apply f
  rw [hae] at hae'
  rw [haf] at haf'
  rw [← hae', triHexPlanarFiniteStar_dualEnds, Sym2.eq_iff] at he
  rw [← haf', triHexPlanarFiniteStar_dualEnds, Sym2.eq_iff] at hf
  have sitePair (u : TriHexPlanarFiniteCell m) (k : Fin 3)
      (hends :
        (triHexPlanarFiniteStarFace m (triHexSpokeFace1 u.1 k) =
            triHexBrickInnerFaceMap N m x ∧
          triHexPlanarFiniteStarFace m (triHexSpokeFace2 u.1 k) =
            triHexBrickInnerFaceMap N m y) ∨
        (triHexPlanarFiniteStarFace m (triHexSpokeFace1 u.1 k) =
            triHexBrickInnerFaceMap N m y ∧
          triHexPlanarFiniteStarFace m (triHexSpokeFace2 u.1 k) =
            triHexBrickInnerFaceMap N m x)) :
      s(triHexSpokeFace1 u.1 k, triHexSpokeFace2 u.1 k) =
        s(x.1, y.1) := by
    rw [Sym2.eq_iff]
    rcases hends with hends | hends
    · exact Or.inl
        ⟨(triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp hends.1,
          (triHexPlanarFiniteStarFace_eq_inner_iff hNm y _).mp hends.2⟩
    · exact Or.inr
        ⟨(triHexPlanarFiniteStarFace_eq_inner_iff hNm y _).mp hends.1,
          (triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp hends.2⟩
  have hze := sitePair z i (by
    simpa [triHexBrickInnerFaceMap] using he)
  have hwe := sitePair w j (by
    simpa [triHexBrickInnerFaceMap] using hf)
  have hchart :
      triangularEdgeChart (triHexIndexEquiv.symm (z.1, i)) =
        triangularEdgeChart (triHexIndexEquiv.symm (w.1, j)) := by
    apply Subtype.ext
    change triangularIndexedEdge (triHexIndexEquiv.symm (z.1, i)) =
      triangularIndexedEdge (triHexIndexEquiv.symm (w.1, j))
    rw [← triHexSpokeFaces_eq_triangularIndexedEdge,
      ← triHexSpokeFaces_eq_triangularIndexedEdge, hze, hwe]
  have hindex : (z.1, i) = (w.1, j) :=
    triHexIndexEquiv.symm.injective
      (triangularEdgeChart_injective hchart)
  have hz : z = w := Subtype.ext (congrArg Prod.fst hindex)
  have hij : i = j := congrArg Prod.snd hindex
  subst w
  subst j
  exact hae'.symm.trans haf'



theorem triHexBrick_pfdEdgeBundle_inner_card_eq_one
    {N m : Nat} (hNm : N < m)
    (a : (triHexBrickInnerTriangleGraph N).edgeFinset) :
    (pfdEdgeBundle (triHexPlanarFiniteStarPlanar m)
      (ocd_innerEdge (triHexBrickInnerFaceMap N m) a.1)).card = 1 := by
  have haAdj : (triHexBrickInnerTriangleGraph N).Adj
      a.1.out.1 a.1.out.2 := by
    have haEdge : a.1 ∈ (triHexBrickInnerTriangleGraph N).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using a.2
    rw [← a.1.out_eq, SimpleGraph.mem_edgeSet] at haEdge
    exact haEdge
  have ha : (triHexBrickFullDualGraph m).Adj
      (triHexBrickInnerFaceMap N m a.1.out.1)
      (triHexBrickInnerFaceMap N m a.1.out.2) :=
    (triHexBrickInnerFaceMap_adj hNm _ _).mp haAdj
  rw [triHexBrickFullDualGraph, BeffaraDC.pfdClosedDual_adj] at ha
  obtain ⟨_, e, _, he⟩ := ha
  have hout : ocd_innerEdge (triHexBrickInnerFaceMap N m) a.1 =
      s(triHexBrickInnerFaceMap N m a.1.out.1,
        triHexBrickInnerFaceMap N m a.1.out.2) := by
    calc
      ocd_innerEdge (triHexBrickInnerFaceMap N m) a.1 =
          ocd_innerEdge (triHexBrickInnerFaceMap N m)
            s(a.1.out.1, a.1.out.2) :=
        congrArg (ocd_innerEdge (triHexBrickInnerFaceMap N m))
          a.1.out_eq.symm
      _ = _ := ocd_innerEdge_mk _ _ _
  apply Finset.card_eq_one.mpr
  refine ⟨e, ?_⟩
  ext f
  rw [Finset.mem_singleton, mem_pfdEdgeBundle]
  constructor
  · intro hf
    exact triHexBrick_edge_eq_of_dualEnds_eq_inner hNm
      (by simpa [hout] using hf) (by simpa [hout] using he)
  · rintro rfl
    simpa [hout] using he



theorem triHexBrick_pfdEffectiveParam_innerEdge
    {N m : Nat} (hNm : N < m) (p : Real)
    (a : (triHexBrickInnerTriangleGraph N).edgeFinset) :
    pfdEffectiveParam (triHexPlanarFiniteStarPlanar m) p
      (ocd_innerEdge (triHexBrickInnerFaceMap N m) a.1) = p := by
  rw [pfdEffectiveParam,
    triHexBrick_pfdEdgeBundle_inner_card_eq_one hNm]
  ring

end

end StatMech.FK.PeriodicPlanar

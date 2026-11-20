/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickFiniteDualComparison
import Code.FK.TriHexPairOrbitCharts





open Finset Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC
open StatMech.FrontierD

noncomputable section


def triHexPlanarFiniteStarEdgeIncl (m : Nat) :
    Sym2 (triHexPlanarFiniteStarPlanar m).V → Sym2 HexVertex :=
  Sym2.map (triHexPlanarFiniteStarVertexEmbedding m)

theorem triHexPlanarFiniteStarEdgeIncl_injective (m : Nat) :
    Function.Injective (triHexPlanarFiniteStarEdgeIncl m) :=
  Sym2.map.injective (triHexPlanarFiniteStarVertexEmbedding m).injective



def triHexPlanarFiniteStarExtendEdge (m : Nat)
    (omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V)) :
    ConfigSpace (Sym2 HexVertex) := fun e =>
  if h : e ∈ Set.range (triHexPlanarFiniteStarEdgeIncl m) then
    omega h.choose
  else false

@[simp] theorem triHexPlanarFiniteStarExtendEdge_edgeIncl
    (m : Nat)
    (omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V))
    (e : Sym2 (triHexPlanarFiniteStarPlanar m).V) :
    triHexPlanarFiniteStarExtendEdge m omega
      (triHexPlanarFiniteStarEdgeIncl m e) = omega e := by
  unfold triHexPlanarFiniteStarExtendEdge
  rw [dif_pos ⟨e, rfl⟩]
  congr 1
  exact triHexPlanarFiniteStarEdgeIncl_injective m
    (Set.mem_range.mp
      (show triHexPlanarFiniteStarEdgeIncl m e ∈
        Set.range (triHexPlanarFiniteStarEdgeIncl m) from ⟨e, rfl⟩)).choose_spec

theorem monotone_triHexPlanarFiniteStarExtendEdge (m : Nat) :
    Monotone (triHexPlanarFiniteStarExtendEdge m) := by
  intro omega eta home e
  unfold triHexPlanarFiniteStarExtendEdge
  by_cases he : e ∈ Set.range (triHexPlanarFiniteStarEdgeIncl m)
  · rw [dif_pos he, dif_pos he]
    exact home _
  · rw [dif_neg he, dif_neg he]



def triHexFaceDualInnerActive (N : Nat)
    (omega : ConfigSpace (Sym2 HexVertex)) :
    ConfigSpace (triangularBoxGraph N).edgeSet := fun a =>
  !(omega (triHexFullDualEdgeEquiv
    (Sym2.map Subtype.val a.1)))

theorem continuous_triHexFaceDualInnerActive (N : Nat) :
    Continuous (triHexFaceDualInnerActive N) := by
  apply continuous_pi
  intro a
  exact (continuous_of_discreteTopology :
    Continuous (fun b : Bool => !b)).comp
      (continuous_apply (triHexFullDualEdgeEquiv
        (Sym2.map Subtype.val a.1)))

theorem antitone_triHexFaceDualInnerActive (N : Nat) :
    Antitone (triHexFaceDualInnerActive N) := by
  intro omega eta home a
  unfold triHexFaceDualInnerActive
  have h := home (triHexFullDualEdgeEquiv
    (Sym2.map Subtype.val a.1))
  cases h1 : omega (triHexFullDualEdgeEquiv
      (Sym2.map Subtype.val a.1)) <;>
    cases h2 : eta (triHexFullDualEdgeEquiv
      (Sym2.map Subtype.val a.1)) <;>
    simp_all

def triHexFaceDualInnerEvent (N : Nat)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    Set (ConfigSpace (Sym2 HexVertex)) :=
  triHexFaceDualInnerActive N ⁻¹' A

theorem isClopen_triHexFaceDualInnerEvent (N : Nat)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    IsClopen (triHexFaceDualInnerEvent N A) :=
  (isClopen_discrete A).preimage
    (continuous_triHexFaceDualInnerActive N)

theorem triHexFaceDualInnerEvent_isDecreasing
    (N : Nat) {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    IsDecreasing (triHexFaceDualInnerEvent N A) := by
  intro eta omega home hmem
  exact hA (antitone_triHexFaceDualInnerActive N home) hmem



theorem triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner
    {N m : Nat} (hNm : N < m)
    {x y : TriangularBoxVertex N}
    {e : kwg_Edge (triHexPlanarFiniteStarPlanar m)}
    (he : kwg_dualEnds (triHexPlanarFiniteStarPlanar m) e =
      s(triHexBrickInnerFaceMap N m x,
        triHexBrickInnerFaceMap N m y)) :
    triHexPlanarFiniteStarEdgeIncl m e.1 =
      triHexFullDualEdgeEquiv s(x.1, y.1) := by
  generalize ha : (triHexPlanarFiniteStarEdgeEquiv m).symm e = a
  rcases a with ⟨z, i⟩
  have heq := (triHexPlanarFiniteStarEdgeEquiv m).apply_symm_apply e
  rw [ha] at heq
  rw [← heq, triHexPlanarFiniteStar_dualEnds, Sym2.eq_iff] at he
  have hpair :
      s(triHexSpokeFace1 z.1 i, triHexSpokeFace2 z.1 i) =
        s(x.1, y.1) := by
    rw [Sym2.eq_iff]
    rcases he with he | he
    · exact Or.inl
        ⟨(triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp he.1,
          (triHexPlanarFiniteStarFace_eq_inner_iff hNm y _).mp he.2⟩
    · exact Or.inr
        ⟨(triHexPlanarFiniteStarFace_eq_inner_iff hNm y _).mp he.1,
          (triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp he.2⟩
  have htri :
      triangularIndexedEdge (triHexIndexEquiv.symm (z.1, i)) =
        s(x.1, y.1) := by
    rw [← triHexSpokeFaces_eq_triangularIndexedEdge]
    exact hpair
  calc
    triHexPlanarFiniteStarEdgeIncl m e.1 =
        hexagonalIndexedEdge (z.1, i) := by
      rw [← heq]
      rfl
    _ = hexagonalIndexedEdge
        (triHexIndexEquiv (triHexIndexEquiv.symm (z.1, i))) := by
      rw [triHexIndexEquiv.apply_symm_apply]
    _ = triHexFullDualEdgeEquiv
        (triangularIndexedEdge (triHexIndexEquiv.symm (z.1, i))) :=
      (triHexFullDualEdgeEquiv_indexedEdge _).symm
    _ = triHexFullDualEdgeEquiv s(x.1, y.1) :=
      congrArg triHexFullDualEdgeEquiv htri



theorem triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual
    {N m : Nat} (hNm : N < m)
    (omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V)) :
    triHexBrickDualInnerActiveRestrict hNm
        (triHexBrickPfdSupport m omega) =
      triHexFaceDualInnerActive N
        (triHexPlanarFiniteStarExtendEdge m omega) := by
  funext a
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      have hxy : (triangularBoxGraph N).Adj x y :=
        (SimpleGraph.mem_edgeSet _).1 ha
      have hfull : (triHexBrickFullDualGraph m).Adj
          (triHexBrickInnerFaceMap N m x)
          (triHexBrickInnerFaceMap N m y) :=
        (triHexBrickInnerFaceMap_adj hNm x y).mp hxy
      obtain ⟨e, heBundle⟩ := pfdEdgeBundle_nonempty_of_fullDualEdge
        (triHexPlanarFiniteStarPlanar m)
        ((SimpleGraph.mem_edgeSet _).2 hfull)
      rw [mem_pfdEdgeBundle] at heBundle
      have heIncl :=
        triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner
          hNm heBundle
      simp only [triHexBrickDualInnerActiveRestrict,
        ocd_innerRestrictActive, triHexBrickPfdSupport,
        pfdIndexedSupportActive, restrictActive, indexedBundleSupport,
        pfdEdgeComplement_apply, triHexFaceDualInnerActive,
        ocd_innerEdge_mk, Sym2.map_mk]
      rw [← heIncl,
        triHexPlanarFiniteStarExtendEdge_edgeIncl]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨f, hf, hopen⟩
        have hfe : f = e :=
          triHexBrick_edge_eq_of_dualEnds_eq_inner hNm hf heBundle
        subst f
        exact hopen
      · intro hopen
        exact ⟨e, heBundle, hopen⟩

end

end StatMech.FK.PeriodicPlanar

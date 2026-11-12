/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWSourceArcPlacement













open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box


def rlc_traceSplitCounterexample_failureAnchor : Sym2 (Site 2) :=
  s((![-1, -1] : Site 2), ![0, -1])

private def rlc_failureSelectedCounterexampleRightSide (z : Site 2) : Prop :=
  z = ![-1, -2] ∨ z = ![-1, -1]

private theorem rlc_failureSelectedCounterexample_not_relaxed_exit :
    ¬ rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap
      (![-1, -2] : Site 2) ![0, -2] := by
  unfold rlc_contourEdgeRelaxedLocal
  rintro (hexposed | ⟨_htarget, hsource⟩)
  · rw [Finset.mem_union] at hexposed
    rcases hexposed with he | he
    · have hz :=
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_traceSplitCounterexampleRight.1 he).2
      rw [rlc_traceSplitCounterexample_right_vertices] at hz
      simp [rlc_dualReflect, rlc_dualReflectFun] at hz
    · have hz :=
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_traceSplitCounterexampleLeft.1 he).1
      rw [rlc_traceSplitCounterexample_left_vertices] at hz
      simp [rlc_dualReflect, rlc_dualReflectFun] at hz
  · unfold rlc_boundarySourceLocallySupported at hsource
    have hshared :
        sharedPrimalEdge (![-1, -2] : Site 2) ![0, -2] =
          s((![0, -2] : Site 2), ![0, -1]) := by
      simpa using sharedPrimalEdge_right' (-1) (-2)
    rcases hsource with hgap | hright | hleft
    · have hmem : (![0, -2] : Site 2) ∈
          sharedPrimalEdge ![-1, -2] ![0, -2] := by
        rw [hshared, Sym2.mem_iff]
        simp
      have hz := hgap.1 _ hmem
      simp [mem_rect] at hz
    · have hmem : (![0, -2] : Site 2) ∈
          sharedPrimalEdge ![-1, -2] ![0, -2] := by
        rw [hshared, Sym2.mem_iff]
        simp
      have hz := rlc_reflectedRightPathEdge_endpoint_mem_box
        rlc_traceSplitCounterexampleRight hright hmem
      simp [mem_rect] at hz
    · have hmem : (![0, -2] : Site 2) ∈
          sharedPrimalEdge ![-1, -2] ![0, -2] := by
        rw [hshared, Sym2.mem_iff]
        simp
      have hz := rlc_reflectedLeftPathEdge_endpoint_mem_box
        rlc_traceSplitCounterexampleLeft hleft hmem
      simp [mem_rect] at hz

private theorem rlc_failureSelectedCounterexampleRightSide_step
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj f g)
    (hlocal : rlc_contourEdgeRelaxedLocal
      rlc_windingSideCounterexampleGap f g)
    (hanchor : s(f, g) ≠ rlc_traceSplitCounterexample_failureAnchor)
    (hf : rlc_failureSelectedCounterexampleRightSide f) :
    rlc_failureSelectedCounterexampleRightSide g := by
  rcases hf with rfl | rfl
  · rcases face_adj_dir hfg.1 with hg | hg | hg | hg <;> subst g
    · exact False.elim
        (rlc_failureSelectedCounterexample_not_relaxed_exit hlocal)
    · exfalso
      have hbd := hfg.2
      norm_num at hbd
      have hshared :
          sharedPrimalEdge (![-1, -2] : Site 2) ![-2, -2] =
            s((![-1, -2] : Site 2), ![-1, -1]) := by
        simpa using sharedPrimalEdge_left' (-1) (-2)
      rw [hK, hshared, bdEdge_mk,
        rlc_traceSplitCounterexample_right_vertices] at hbd
      simp at hbd
    · exact Or.inr rfl
    · exfalso
      have hbd := hfg.2
      norm_num at hbd
      have hshared :
          sharedPrimalEdge (![-1, -2] : Site 2) ![-1, -3] =
            s((![-1, -2] : Site 2), ![0, -2]) := by
        simpa using sharedPrimalEdge_bottom' (-1) (-2)
      rw [hK, hshared, bdEdge_mk,
        rlc_traceSplitCounterexample_right_vertices] at hbd
      simp at hbd
  · rcases face_adj_dir hfg.1 with hg | hg | hg | hg <;> subst g
    · exfalso
      apply hanchor
      rfl
    · exfalso
      have hbd := hfg.2
      norm_num at hbd
      have hshared :
          sharedPrimalEdge (![-1, -1] : Site 2) ![-2, -1] =
            s((![-1, -1] : Site 2), ![-1, 0]) := by
        simpa using sharedPrimalEdge_left' (-1) (-1)
      rw [hK, hshared, bdEdge_mk,
        rlc_traceSplitCounterexample_right_vertices] at hbd
      simp at hbd
    · exfalso
      have hbd := hfg.2
      norm_num at hbd
      have hshared :
          sharedPrimalEdge (![-1, -1] : Site 2) ![-1, 0] =
            s((![-1, 0] : Site 2), ![0, 0]) := by
        simpa using sharedPrimalEdge_top' (-1) (-1)
      rw [hK, hshared, bdEdge_mk,
        rlc_traceSplitCounterexample_right_vertices] at hbd
      simp at hbd
    · exact Or.inl rfl

private theorem rlc_failureSelectedCounterexampleRightSide_walk
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
    {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Walk x y)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap f g)
    (hanchor : rlc_traceSplitCounterexample_failureAnchor ∉ a.edges)
    (hx : rlc_failureSelectedCounterexampleRightSide x) :
    rlc_failureSelectedCounterexampleRightSide y := by
  induction a with
  | nil => exact hx
  | @cons u v z huv p ih =>
      have huvLocal : rlc_contourEdgeRelaxedLocal
          rlc_windingSideCounterexampleGap u v :=
        hlocal (by simp)
      have huvAnchor : s(u, v) ≠ rlc_traceSplitCounterexample_failureAnchor := by
        intro heq
        apply hanchor
        simp [heq]
      have hv := rlc_failureSelectedCounterexampleRightSide_step
        omega hK huv huvLocal huvAnchor hx
      apply ih
      · intro f g hfg
        exact hlocal (by simp [hfg])
      · intro he
        exact hanchor (by simp [he])
      · exact hv

private theorem rlc_failureSelectedCounterexample_no_boundary_adj_negTwoNegTwo
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
    {z : Site 2}
    (hz : (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![-2, -2] z) : False := by
  rcases face_adj_dir hz.1 with h | h | h | h <;> subst z <;>
    have hbd := hz.2 <;> norm_num at hbd <;>
    rw [hK, rlc_traceSplitCounterexample_right_vertices] at hbd <;>
    simp [sharedPrimalEdge, bdEdge] at hbd

private theorem rlc_failureSelectedCounterexample_no_boundary_adj_negThreeNegTwo
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
    {z : Site 2}
    (hz : (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![-3, -2] z) : False := by
  rcases face_adj_dir hz.1 with h | h | h | h <;> subst z <;>
    have hbd := hz.2 <;> norm_num at hbd <;>
    rw [hK, rlc_traceSplitCounterexample_right_vertices] at hbd <;>
    simp [sharedPrimalEdge, bdEdge] at hbd

private theorem rlc_failureSelectedCounterexample_no_boundary_adj_negThreeNegOne
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
    {z : Site 2}
    (hz : (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![-3, -1] z) : False := by
  rcases face_adj_dir hz.1 with h | h | h | h <;> subst z <;>
    have hbd := hz.2 <;> norm_num at hbd <;>
    rw [hK, rlc_traceSplitCounterexample_right_vertices] at hbd <;>
    simp [sharedPrimalEdge, bdEdge] at hbd

private theorem rlc_failureSelectedCounterexample_rightContact_eq
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
    {x z : Site 2}
    (hx : rlc_dualReflect x ∈
      rlc_pathVertices rlc_traceSplitCounterexampleRight.1)
    (hxz : (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj x z) :
    x = ![-1, -2] := by
  have hxCases :
      x = ![-1, -2] ∨ x = ![-2, -2] ∨
        x = ![-3, -2] ∨ x = ![-3, -1] := by
    rw [rlc_traceSplitCounterexample_right_vertices] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx
    · left
      apply rlc_dualReflect.injective
      simpa [rlc_dualReflect, rlc_dualReflectFun] using hx
    · right; left
      apply rlc_dualReflect.injective
      simpa [rlc_dualReflect, rlc_dualReflectFun] using hx
    · right; right; left
      apply rlc_dualReflect.injective
      simpa [rlc_dualReflect, rlc_dualReflectFun] using hx
    · right; right; right
      apply rlc_dualReflect.injective
      simpa [rlc_dualReflect, rlc_dualReflectFun] using hx
  rcases hxCases with rfl | rfl | rfl | rfl
  · rfl
  · exact False.elim
      (rlc_failureSelectedCounterexample_no_boundary_adj_negTwoNegTwo
        omega hK hxz)
  · exact False.elim
      (rlc_failureSelectedCounterexample_no_boundary_adj_negThreeNegTwo
        omega hK hxz)
  · exact False.elim
      (rlc_failureSelectedCounterexample_no_boundary_adj_negThreeNegOne
        omega hK hxz)

private theorem rlc_failureSelectedCounterexample_leftContact_not_rightSide
    {y : Site 2}
    (hy : rlc_dualReflect y ∈
      rlc_pathVertices rlc_traceSplitCounterexampleLeft.1) :
    ¬ rlc_failureSelectedCounterexampleRightSide y := by
  intro hySide
  rcases hySide with rfl | rfl
  · rw [rlc_traceSplitCounterexample_left_vertices] at hy
    simp [rlc_dualReflect, rlc_dualReflectFun] at hy
  · rw [rlc_traceSplitCounterexample_left_vertices] at hy
    simp [rlc_dualReflect, rlc_dualReflectFun] at hy




theorem rlc_traceSplitCounterexample_anchor_mem_of_relaxedTraceArc
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
    {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Walk x y)
    (hx : rlc_dualReflect x ∈
      rlc_pathVertices rlc_traceSplitCounterexampleRight.1)
    (hy : rlc_dualReflect y ∈
      rlc_pathVertices rlc_traceSplitCounterexampleLeft.1)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap f g) :
    rlc_traceSplitCounterexample_failureAnchor ∈ a.edges := by
  by_contra hanchor
  have hxy : x ≠ y := by
    intro hxy
    subst y
    rw [rlc_traceSplitCounterexample_right_vertices] at hx
    rw [rlc_traceSplitCounterexample_left_vertices] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx | hx | hx <;>
      rcases hy with hy | hy | hy | hy <;> simp_all
  have hnonNil : ¬ a.Nil := SimpleGraph.Walk.not_nil_of_ne hxy
  have hxEq := rlc_failureSelectedCounterexample_rightContact_eq
    omega hK hx (a.adj_snd hnonNil)
  have hxSide : rlc_failureSelectedCounterexampleRightSide x :=
    Or.inl hxEq
  have hySide := rlc_failureSelectedCounterexampleRightSide_walk
    omega hK a hlocal hanchor hxSide
  exact rlc_failureSelectedCounterexample_leftContact_not_rightSide hy hySide



theorem rlc_traceSplitCounterexample_not_carries_of_anchor_not_mem
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)))
    {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Walk u v)
    (hanchor : rlc_traceSplitCounterexample_failureAnchor ∉ p.edges) :
    ¬ RlcFaceBoundaryWalkCarriesRelaxedTraceArc
      rlc_windingSideCounterexampleGap omega p := by
  rintro ⟨x, y, a, hsub, hx, hy, hlocal⟩
  have ha := rlc_traceSplitCounterexample_anchor_mem_of_relaxedTraceArc
    omega hK a hx hy hlocal
  exact hanchor (hsub _ ha)





theorem rlc_windingSideCounterexample_not_failureComplementaryArcEscapes :
    ¬ RlcFailureComplementaryArcEscapesDefectCut
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig := by
  rintro ⟨t, f, g, p, htLower, htUpper, htIn, _htOut,
    hfg, hshared, hanchor, hcarry⟩
  have htCases : t = -1 ∨ t = 0 := by
    change (-1 : ℤ) ≤ t at htLower
    change t < 1 at htUpper
    omega
  have ht : t = -1 := by
    rcases htCases with ht | ht
    · exact ht
    · subst t
      rw [rlc_windingSideCounterexample_reachSet_eq,
        rlc_traceSplitCounterexample_right_vertices] at htIn
      simp at htIn
  subst t
  norm_num at hshared
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, -1] : Site 2) ![0, -1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, -1] : Site 2) ![0, -1] =
        s((![0, -1] : Site 2), ![0, 0]) := by
    simpa using sharedPrimalEdge_right' (-1) (-1)
  have hedge : s(f, g) = rlc_traceSplitCounterexample_failureAnchor := by
    unfold rlc_traceSplitCounterexample_failureAnchor
    exact sharedPrimalEdge_uncrossInj hfg.1 hcanonicalAdj
      (hshared.trans hcanonicalShared.symm)
  have hcanonicalNot :
      rlc_traceSplitCounterexample_failureAnchor ∉ p.edges := by
    rwa [← hedge]
  exact (rlc_traceSplitCounterexample_not_carries_of_anchor_not_mem
    rlc_windingSideCounterexampleConfig
    rlc_windingSideCounterexample_reachSet_eq p hcanonicalNot) hcarry





theorem rlc_windingSideCounterexample_failure_selected_obstruction :
    rlc_windingSideCounterexampleConfig ∉
        rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧
      ¬ RlcFailureComplementaryArcEscapesDefectCut
        rlc_windingSideCounterexampleGap
        rlc_windingSideCounterexampleConfig ∧
      RlcRelaxedLocalTraceArcExists
        rlc_windingSideCounterexampleGap
        rlc_windingSideCounterexampleConfig := by
  refine ⟨rlc_windingSideCounterexample_failure,
    rlc_windingSideCounterexample_not_failureComplementaryArcEscapes, ?_⟩
  refine ⟨![-1, -2], ![1, -1],
    rlc_traceSplitCounterexample_boundaryArc
      rlc_windingSideCounterexampleConfig
      rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_boundaryArc_rightContact,
    rlc_traceSplitCounterexample_boundaryArc_leftContact, ?_⟩
  exact rlc_traceSplitCounterexample_boundaryArc_relaxed
    rlc_windingSideCounterexampleConfig
    rlc_windingSideCounterexample_reachSet_eq

end Universality
end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorCentralFaceScaleOneAudit











open Finset SimpleGraph Set
namespace StatMech.Universality
open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

private theorem wall_right :
    s((![1, 0] : Site 2), ![1, 1]) ∈
      rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorFourTraceEdges]
  apply Finset.mem_union_right
  rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
  right
  rw [rlc_reflectedPathEdges]
  apply Finset.mem_image.mpr
  refine ⟨s((![-1, 0] : Site 2), ![-1, 1]), ?_, ?_⟩
  · rw [rlc_axisReturnCounterexample_left_edges]
    simp
  · simp [rlc_flipX, rlc_flipXFun, Sym2.map_mk]

private theorem wall_left :
    s((![0, 0] : Site 2), ![0, 1]) ∈
      rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorFourTraceEdges]
  apply Finset.mem_union_left
  rw [Finset.mem_union]
  right
  rw [rlc_axisReturnCounterexample_left_edges]
  simp

private theorem wall_bottom :
    s((![0, 0] : Site 2), ![1, 0]) ∈
      rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorFourTraceEdges]
  apply Finset.mem_union_right
  rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
  right
  rw [rlc_reflectedPathEdges]
  apply Finset.mem_image.mpr
  refine ⟨s((![-1, 0] : Site 2), ![0, 0]), ?_, ?_⟩
  · rw [rlc_axisReturnCounterexample_left_edges]
    simp
  · simpa [rlc_flipX, rlc_flipXFun, Sym2.map_mk] using
      (Sym2.eq_swap : s((![1, 0] : Site 2), ![0, 0]) =
        s(![0, 0], ![1, 0]))

private theorem isolated (z : RlcConnectorFaceVertex 1) :
    ¬ (rlc_connectorFiniteFaceCutGraph rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft).Adj
        ⟨rlc_connectorCentralFace,
          rlc_connectorCentralFace_mem_faceBox (by norm_num)⟩ z := by
  intro h
  change (rlc_connectorFourTraceFaceCutGraph
    rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft).Adj
      rlc_connectorCentralFace (z : Site 2) at h
  rw [rlc_connectorFourTraceFaceCutGraph_adj] at h
  rcases face_adj_dir h.1 with hz | hz | hz | hz
  · have : (z : Site 2) = ![1, 0] := by simpa [rlc_connectorCentralFace] using hz
    rw [this] at h
    apply h.2
    simpa [rlc_connectorCentralFace, sharedPrimalEdge] using wall_right
  · have : (z : Site 2) = ![-1, 0] := by simpa [rlc_connectorCentralFace] using hz
    rw [this] at h
    apply h.2
    simpa [rlc_connectorCentralFace, sharedPrimalEdge] using wall_left
  · have : (z : Site 2) = ![0, 1] := by simpa [rlc_connectorCentralFace] using hz
    have hzbox := z.2
    rw [this] at hzbox
    simp [rlc_connectorFaceBox, mem_rect] at hzbox
  · have : (z : Site 2) = ![0, -1] := by simpa [rlc_connectorCentralFace] using hz
    rw [this] at h
    apply h.2
    simpa [rlc_connectorCentralFace, sharedPrimalEdge] using wall_bottom

theorem rlc_axisReturnCounterexample_centralFaceRegion_eq_singleton :
    rlc_connectorCentralFaceRegion rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft = {rlc_connectorCentralFace} := by
  ext f
  constructor
  · intro hf
    have hfset : f ∈ rlc_connectorCentralFaceRegionSet
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
      simpa [rlc_connectorCentralFaceRegion] using hf
    obtain ⟨hfb, hsb, hreach⟩ := hfset
    obtain ⟨w⟩ := hreach
    cases w with
    | nil => simp
    | cons hfirst _ => exact False.elim (isolated _ hfirst)
  · intro hf
    simp only [Finset.mem_singleton] at hf
    subst f
    exact rlc_connectorCentralFace_mem_region _ _ (by norm_num)

def rlc_axisReturnCounterexampleClosedConfig :
    ConfigSpace (Sym2 (RlcConnectorVertex 1)) :=
  fun _ => false

theorem rlc_axisReturnCounterexample_source_failure :
    rlc_axisReturnCounterexampleClosedConfig ∉
      rlc_finiteCentralFaceRandomConnectorEvent
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  have hopen : FK.openSub
      (rlc_connectorCentralFaceFiniteGraph
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft)
      rlc_axisReturnCounterexampleClosedConfig = ⊥ := by
    ext u v
    simp [FK.openSub_adj, rlc_axisReturnCounterexampleClosedConfig]
  rw [hopen] at hxy
  have hxyEq : x = y := SimpleGraph.reachable_bot.mp hxy
  subst y
  rw [rlc_connectorOnRight] at hx
  rw [rlc_connectorOnLeft] at hy
  exact Finset.disjoint_left.mp
    rlc_axisReturnCounterexample_bookPositioned.exposed_disjoint hx hy

private theorem not_fourTrace
    {e : Sym2 (Site 2)}
    (he : e = s((![0, -1] : Site 2), ![0, 0]) ∨
      e = s((![1, -1] : Site 2), ![1, 0]) ∨
      e = s((![1, 0] : Site 2), ![2, 0])) :
    e ∉ rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft := by
  rcases he with rfl | rfl | rfl
  all_goals
    rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges,
      rlc_reflectedPathEdges,
      rlc_traceSplitCounterexample_right_edges,
      rlc_axisReturnCounterexample_left_edges]
    simp [rlc_reflectedPathEdges, rlc_flipX, rlc_flipXFun,
      Sym2.map_mk]
    all_goals
      intro x hx
      have hx' : x ∈
          ({s((![-2, 0] : Site 2), ![-2, 1]),
            s((![-2, 1] : Site 2), ![-1, 1]),
            s((![-1, 1] : Site 2), ![-1, 0]),
            s((![-1, 0] : Site 2), ![0, 0]),
            s((![0, 0] : Site 2), ![0, 1])} : Finset (Sym2 (Site 2))) := by
        simpa only [rlc_axisReturnCounterexample_left_edges] using hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
        simp [Sym2.map_mk]

private theorem not_closure
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y)
    (hface : rlc_connectorCentralFace ∉ flankFaces x y) :
    s(x, y) ∉ rlc_connectorCentralFaceClosureEdges
      rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  intro he
  rw [rlc_connectorCentralFaceClosureEdges, Finset.mem_filter] at he
  obtain ⟨_hebox, f, hf, hfe⟩ := he
  rw [rlc_axisReturnCounterexample_centralFaceRegion_eq_singleton] at hf
  simp only [Finset.mem_singleton] at hf
  subst f
  rw [StatMech.FrontierD.fci_faceEdgeEquiv_symm_mk_of_adj hxy] at hfe
  exact hface hfe

private theorem bad_c_not_planar :
    s((![0, -1] : Site 2), ![0, 0]) ∉
      rlc_connectorCentralFacePlanarEdges
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union]
  push Not
  constructor
  · apply not_closure
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [rlc_connectorCentralFace, flankFaces]
  · exact not_fourTrace (Or.inl rfl)

private theorem bad_d_not_planar :
    s((![1, -1] : Site 2), ![1, 0]) ∉
      rlc_connectorCentralFacePlanarEdges
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union]
  push Not
  constructor
  · apply not_closure
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [rlc_connectorCentralFace, flankFaces]
  · exact not_fourTrace (Or.inr (Or.inl rfl))

private theorem bad_e_not_planar :
    s((![1, 0] : Site 2), ![2, 0]) ∉
      rlc_connectorCentralFacePlanarEdges
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union]
  push Not
  constructor
  · apply not_closure
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [rlc_connectorCentralFace, flankFaces]
  · exact not_fourTrace (Or.inr (Or.inr rfl))

private def BottomComponentSide (z : Site 2) : Prop :=
  z 1 = -1 ∨ z 0 = 2

private theorem crossing_cases {x y : Site 2}
    (hx : x ∈ rect (-2) 2 (-1) 1)
    (hy : y ∈ rect (-2) 2 (-1) 1)
    (hadj : (hypercubicLattice 2).Adj x y)
    (hsplit : BottomComponentSide x ↔ ¬ BottomComponentSide y) :
    s(x, y) = s((![-2, -1] : Site 2), ![-2, 0]) ∨
      s(x, y) = s((![-1, -1] : Site 2), ![-1, 0]) ∨
      s(x, y) = s((![0, -1] : Site 2), ![0, 0]) ∨
      s(x, y) = s((![1, -1] : Site 2), ![1, 0]) ∨
      s(x, y) = s((![1, 0] : Site 2), ![2, 0]) ∨
    s(x, y) = s((![1, 1] : Site 2), ![2, 1]) := by
  rw [mem_rect] at hx hy
  have hx0Lower : -2 ≤ x 0 := hx.1
  have hx0Upper : x 0 ≤ 2 := hx.2.1
  have hx1Lower : -1 ≤ x 1 := hx.2.2.1
  have hx1Upper : x 1 ≤ 1 := hx.2.2.2
  have hxrepr : x = ![x 0, x 1] := by
    ext i
    fin_cases i <;> rfl
  rcases face_adj_dir hadj with h | h | h | h <;> subst y
  all_goals
    interval_cases hx0 : x 0 <;>
      interval_cases hx1 : x 1 <;>
      simp_all [BottomComponentSide]

private theorem pims_closed_a :
    rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft
        rlc_axisReturnCounterexampleClosedConfig
      s(⟨![-2, -1], by simp [mem_rect]⟩,
        ⟨![-2, 0], by simp [mem_rect]⟩) = false := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![-2, -1] : Site 2), ![-2, 0]) =
        s((![1, -1] : Site 2), ![2, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical (-2) (-1)
  rw [show (s(⟨![-2, -1], by simp [mem_rect]⟩,
      ⟨![-2, 0], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![-2, -1] : Site 2), ![-2, 0]) by rfl, hpims]
  have htrace : s((![1, -1] : Site 2), ![2, -1]) ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_axisReturnCounterexampleLeft.1 := by
    rw [rlc_traceSplitCounterexample_right_edges]
    simp
  rw [rlc_connectorCentralFaceAmbientConfig_trace _ _ _ htrace]
  rfl

private theorem pims_closed_b :
    rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft
        rlc_axisReturnCounterexampleClosedConfig
      s(⟨![-1, -1], by simp [mem_rect]⟩,
        ⟨![-1, 0], by simp [mem_rect]⟩) = false := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![-1, -1] : Site 2), ![-1, 0]) =
        s((![0, -1] : Site 2), ![1, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical (-1) (-1)
  rw [show (s(⟨![-1, -1], by simp [mem_rect]⟩,
      ⟨![-1, 0], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![-1, -1] : Site 2), ![-1, 0]) by rfl, hpims]
  have htrace : s((![0, -1] : Site 2), ![1, -1]) ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_axisReturnCounterexampleLeft.1 := by
    rw [rlc_traceSplitCounterexample_right_edges]
    simp
  rw [rlc_connectorCentralFaceAmbientConfig_trace _ _ _ htrace]
  rfl

private theorem pims_closed_f :
    rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft
        rlc_axisReturnCounterexampleClosedConfig
      s(⟨![1, 1], by simp [mem_rect]⟩,
        ⟨![2, 1], by simp [mem_rect]⟩) = false := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![1, 1] : Site 2), ![2, 1]) =
        s((![-2, 0] : Site 2), ![-2, 1]) := by
    simpa using rlc_pimsEdgeEquiv_horizontal 1 1
  rw [show (s(⟨![1, 1], by simp [mem_rect]⟩,
      ⟨![2, 1], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![1, 1] : Site 2), ![2, 1]) by rfl, hpims]
  have htrace : s((![-2, 0] : Site 2), ![-2, 1]) ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_axisReturnCounterexampleLeft.1 := by
    rw [rlc_axisReturnCounterexample_left_edges]
    simp
  rw [rlc_connectorCentralFaceAmbientConfig_trace _ _ _ htrace]
  rfl

private theorem pims_adj_same_side {x y : RlcConnectorVertex 1}
    (hxy : (FK.openSub
      (rlc_connectorCentralFaceClosureGraph
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft)
      (rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft
          rlc_axisReturnCounterexampleClosedConfig)).Adj x y) :
    BottomComponentSide x ↔ BottomComponentSide y := by
  rw [FK.openSub_adj] at hxy
  by_contra hsame
  have hsplit : BottomComponentSide (x : Site 2) ↔
      ¬ BottomComponentSide (y : Site 2) := by
    by_cases hx : BottomComponentSide (x : Site 2) <;>
      by_cases hy : BottomComponentSide (y : Site 2) <;>
      simp_all
  obtain h | h | h | h | h | h := crossing_cases x.2 y.2 hxy.1.1 hsplit
  · have heq : s(x, y) =
        s(⟨![-2, -1], by simp [mem_rect]⟩,
          ⟨![-2, 0], by simp [mem_rect]⟩) := by
      apply Sym2.map.injective Subtype.val_injective
      simpa [Sym2.map_mk] using h
    have hopen := hxy.2
    rw [heq, pims_closed_a] at hopen
    simp at hopen
  · have heq : s(x, y) =
        s(⟨![-1, -1], by simp [mem_rect]⟩,
          ⟨![-1, 0], by simp [mem_rect]⟩) := by
      apply Sym2.map.injective Subtype.val_injective
      simpa [Sym2.map_mk] using h
    have hopen := hxy.2
    rw [heq, pims_closed_b] at hopen
    simp at hopen
  · exact bad_c_not_planar (h ▸ hxy.1.2)
  · exact bad_d_not_planar (h ▸ hxy.1.2)
  · exact bad_e_not_planar (h ▸ hxy.1.2)
  · have heq : s(x, y) =
        s(⟨![1, 1], by simp [mem_rect]⟩,
          ⟨![2, 1], by simp [mem_rect]⟩) := by
      apply Sym2.map.injective Subtype.val_injective
      simpa [Sym2.map_mk] using h
    have hopen := hxy.2
    rw [heq, pims_closed_f] at hopen
    simp at hopen

private theorem pims_walk_stays_side {x y : RlcConnectorVertex 1}
    (w : (FK.openSub
      (rlc_connectorCentralFaceClosureGraph
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft)
      (rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft
          rlc_axisReturnCounterexampleClosedConfig)).Walk x y)
    (hx : BottomComponentSide x) : BottomComponentSide y := by
  induction w with
  | nil => exact hx
  | @cons u v z huv w ih =>
      exact ih ((pims_adj_same_side huv).mp hx)

theorem rlc_axisReturnCounterexample_PIMS_failure :
    rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft
          rlc_axisReturnCounterexampleClosedConfig ∉
      rlc_finiteCentralFaceClosureConnectorEvent
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hxSide : BottomComponentSide x := by
    rw [rlc_connectorOnRight,
      rlc_traceSplitCounterexample_right_vertices] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx
    all_goals
      rw [BottomComponentSide, hx]
      simp
  have hyNot : ¬ BottomComponentSide y := by
    intro hySide
    rw [rlc_connectorOnLeft,
      rlc_axisReturnCounterexample_left_vertices] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy
    all_goals
      rw [BottomComponentSide, hy] at hySide
      simp at hySide
  obtain ⟨w⟩ := hxy
  exact hyNot (pims_walk_stays_side w hxSide)

theorem rlc_axisReturnCounterexample_positioned_doubleFailure :
    RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft ∧
      rlc_axisReturnCounterexampleClosedConfig ∉
        rlc_finiteCentralFaceRandomConnectorEvent
          rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft ∧
      rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
          rlc_axisReturnCounterexampleLeft
            rlc_axisReturnCounterexampleClosedConfig ∉
        rlc_finiteCentralFaceClosureConnectorEvent
          rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft :=
  ⟨rlc_axisReturnCounterexample_bookPositioned,
    rlc_axisReturnCounterexample_source_failure,
    rlc_axisReturnCounterexample_PIMS_failure⟩

end
end StatMech.Universality

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorSeededMassObstruction
import Code.Lattice.WhitneyBridge












open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section


def rlc_connectorFourTraceWallGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧
    s(x, y) ∈ rlc_connectorFourTraceEdges gamma gamma'
  symm := by
    rintro x y ⟨hxy, he⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using he⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorFourTraceWallGraphDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorFourTraceWallGraph gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_mem_fourTraceWallGraph_edgeSet_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
    e ∈ (rlc_connectorFourTraceWallGraph gamma gamma').edgeSet ↔
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at hlat ⊢
      exact and_iff_right hlat

theorem rlc_mem_connectorBarrier_of_mem_fourTraceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e) :
    z ∈ rlc_connectorBarrier gamma gamma' := by
  rw [rlc_connectorFourTraceEdges, Finset.mem_union] at he
  rcases he with horiginal | hreflected
  · rw [Finset.mem_union] at horiginal
    rcases horiginal with hright | hleft
    · induction e using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl <;>
            simp [rlc_connectorBarrier, hends.1, hends.2]
    · induction e using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl <;>
            simp [rlc_connectorBarrier, hends.1, hends.2]
  · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union] at hreflected
    rcases hreflected with hright | hleft
    · obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp hright
      induction e0 using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he0
          have heq' : e = s(rlc_flipX x, rlc_flipX y) := by
            simpa [Sym2.map_mk] using heq.symm
          rw [heq', Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · simp [rlc_connectorBarrier, hends.1]
          · simp [rlc_connectorBarrier, hends.2]
    · obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp hleft
      induction e0 using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 he0
          have heq' : e = s(rlc_flipX x, rlc_flipX y) := by
            simpa [Sym2.map_mk] using heq.symm
          rw [heq', Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · simp [rlc_connectorBarrier, hends.1]
          · simp [rlc_connectorBarrier, hends.2]


noncomputable def rlc_connectorFourTraceFaceCutGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (Site 2) :=
  whb_faceRegion (rlc_connectorFourTraceWallGraph gamma gamma')

theorem rlc_connectorFourTraceFaceCutGraph_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) :
    (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧
        sharedPrimalEdge f g ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
  rw [rlc_connectorFourTraceFaceCutGraph, whb_faceRegion_adj]
  constructor
  · rintro ⟨hfg, hwall⟩
    refine ⟨hfg, ?_⟩
    have hlat : sharedPrimalEdge f g ∈ (hypercubicLattice 2).edgeSet := by
      obtain ⟨u, v, huv, huvAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg
      rw [huv, SimpleGraph.mem_edgeSet]
      exact huvAdj
    rwa [rlc_mem_fourTraceWallGraph_edgeSet_iff gamma gamma' hlat] at hwall
  · rintro ⟨hfg, htrace⟩
    refine ⟨hfg, ?_⟩
    have hlat : sharedPrimalEdge f g ∈ (hypercubicLattice 2).edgeSet := by
      obtain ⟨u, v, huv, huvAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg
      rw [huv, SimpleGraph.mem_edgeSet]
      exact huvAdj
    rwa [rlc_mem_fourTraceWallGraph_edgeSet_iff gamma gamma' hlat]


noncomputable def rlc_connectorFaceBox (n : Int) : Finset (Site 2) :=
  (rect_finite (-2 * n) (2 * n - 1) (-n) (n - 1)).toFinset



def rlc_connectorCentralFace : Site 2 := ![0, 0]

theorem rlc_connectorCentralFace_mem_faceBox {n : Int} (hn : 0 < n) :
    rlc_connectorCentralFace ∈ rlc_connectorFaceBox n := by
  simp [rlc_connectorCentralFace, rlc_connectorFaceBox, mem_rect]
  omega

abbrev RlcConnectorFaceVertex (n : Int) :=
  {f : Site 2 // f ∈ rlc_connectorFaceBox n}


def rlc_connectorFiniteFaceCutGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorFaceVertex n) :=
  (rlc_connectorFourTraceFaceCutGraph gamma gamma').induce
    (rlc_connectorFaceBox n : Set (Site 2))

noncomputable instance rlc_connectorFiniteFaceCutGraphDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj :=
  Classical.decRel _


def rlc_connectorCentralFaceRegionSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (Site 2) :=
  {f | ∃ (hf : f ∈ rlc_connectorFaceBox n)
      (hs : rlc_connectorCentralFace ∈ rlc_connectorFaceBox n),
    (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨rlc_connectorCentralFace, hs⟩ ⟨f, hf⟩}

theorem rlc_connectorCentralFaceRegionSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorCentralFaceRegionSet gamma gamma').Finite := by
  apply (rlc_connectorFaceBox n).finite_toSet.subset
  rintro f ⟨hf, _hs, _hreach⟩
  exact hf

noncomputable def rlc_connectorCentralFaceRegion {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Site 2) :=
  (rlc_connectorCentralFaceRegionSet_finite gamma gamma').toFinset

theorem rlc_connectorCentralFace_mem_region {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hn : 0 < n) :
    rlc_connectorCentralFace ∈
      rlc_connectorCentralFaceRegion gamma gamma' := by
  have hs := rlc_connectorCentralFace_mem_faceBox hn
  have hset : rlc_connectorCentralFace ∈
      rlc_connectorCentralFaceRegionSet gamma gamma' :=
    ⟨hs, hs, ⟨SimpleGraph.Walk.nil⟩⟩
  simpa [rlc_connectorCentralFaceRegion] using hset




theorem rlc_connectorCentralFaceRegion_of_cut_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {f g : Site 2}
    (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hgBox : g ∈ rlc_connectorFaceBox n)
    (hfg : (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj f g) :
    g ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  have hfSet : f ∈ rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hf
  obtain ⟨hfBox, hs, hreach⟩ := hfSet
  have hstep : (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj
      ⟨f, hfBox⟩ ⟨g, hgBox⟩ := hfg
  have hgSet : g ∈ rlc_connectorCentralFaceRegionSet gamma gamma' :=
    ⟨hgBox, hs, hreach.trans hstep.reachable⟩
  simpa [rlc_connectorCentralFaceRegion] using hgSet

theorem rlc_connectorCentralFaceRegion_of_cut_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {f g : Site 2}
    (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hfBox : f ∈ rlc_connectorFaceBox n)
    (hgBox : g ∈ rlc_connectorFaceBox n)
    (hfg : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨f, hfBox⟩ ⟨g, hgBox⟩) :
    g ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  have hfSet : f ∈ rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hf
  obtain ⟨_hfBox, hs, hcentral⟩ := hfSet
  have hfEq : (⟨f, hfBox⟩ : RlcConnectorFaceVertex n) = ⟨f, _hfBox⟩ := rfl
  rw [hfEq] at hfg
  have hgSet : g ∈ rlc_connectorCentralFaceRegionSet gamma gamma' :=
    ⟨hgBox, hs, hcentral.trans hfg⟩
  simpa [rlc_connectorCentralFaceRegion] using hgSet




noncomputable def rlc_connectorCentralFaceClosureEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  (edgesWithinFinset (rlc_connectorBox n)).filter fun e =>
    ∃ f ∈ rlc_connectorCentralFaceRegion gamma gamma',
      f ∈ fci_faceEdgeEquiv.symm e



noncomputable def rlc_connectorCentralFaceEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  rlc_connectorCentralFaceClosureEdges gamma gamma' \
    rlc_connectorFourTraceEdges gamma gamma'




noncomputable def rlc_connectorCentralFacePlanarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  rlc_connectorCentralFaceClosureEdges gamma gamma' ∪
    rlc_connectorFourTraceEdges gamma gamma'

theorem rlc_fci_faceEdgeEquiv_symm_mk_of_adj
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    fci_faceEdgeEquiv.symm s(x, y) = flankFaces x y := by
  obtain ⟨f, g, hfg, hfgAdj⟩ := flankFaces_latAdj hxy
  apply fci_faceEdgeEquiv.injective
  rw [fci_faceEdgeEquiv.apply_symm_apply, hfg,
    fci_faceEdgeEquiv_mk_of_adj hfgAdj, ← symPrimal_eq_shared hfgAdj,
    ← symPrimalSym_mk, ← hfg, symPrimalSym_flankFaces hxy]





theorem rlc_mem_connectorCentralFaceClosureEdges_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    s(x, y) ∈ rlc_connectorCentralFaceClosureEdges gamma gamma' ↔
      x ∈ rlc_connectorBox n ∧ y ∈ rlc_connectorBox n ∧
        ∃ f ∈ rlc_connectorCentralFaceRegion gamma gamma',
          f ∈ flankFaces x y := by
  rw [rlc_connectorCentralFaceClosureEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hbox, f, hf, hfe⟩
    rw [mem_edgesWithinFinset] at hbox
    obtain ⟨u, hu, v, hv, huv⟩ := hbox
    have huv' : s(u, v) = s(x, y) := huv.symm
    have hends : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
      simpa [Sym2.eq_iff] using huv'
    rcases hends with huvEq | huvEq
    · rcases huvEq with ⟨huv1, huv2⟩
      subst u
      subst v
      refine ⟨hu, hv, f, hf, ?_⟩
      rwa [rlc_fci_faceEdgeEquiv_symm_mk_of_adj hxy] at hfe
    · rcases huvEq with ⟨huv1, huv2⟩
      subst u
      subst v
      refine ⟨hv, hu, f, hf, ?_⟩
      rw [rlc_fci_faceEdgeEquiv_symm_mk_of_adj hxy] at hfe
      exact hfe
  · rintro ⟨hx, hy, f, hf, hflank⟩
    refine ⟨?_, f, hf, ?_⟩
    · rw [mem_edgesWithinFinset]
      exact ⟨x, hx, y, hy, rfl⟩
    · rw [rlc_fci_faceEdgeEquiv_symm_mk_of_adj hxy]
      exact hflank



theorem rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y)
    (hx : x ∈ rlc_connectorBox n) (hy : y ∈ rlc_connectorBox n)
    {f : Site 2}
    (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hflank : f ∈ flankFaces x y) :
    s(x, y) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  apply Finset.mem_union_left
  exact (rlc_mem_connectorCentralFaceClosureEdges_iff
    gamma gamma' hxy).2 ⟨hx, hy, f, hf, hflank⟩

theorem rlc_mem_connectorCentralFacePlanarEdges_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    s(x, y) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ↔
      s(x, y) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨
        (x ∈ rlc_connectorBox n ∧ y ∈ rlc_connectorBox n ∧
          ∃ f ∈ rlc_connectorCentralFaceRegion gamma gamma',
            f ∈ flankFaces x y) := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union,
    rlc_mem_connectorCentralFaceClosureEdges_iff gamma gamma' hxy]
  exact or_comm

theorem rlc_connectorCentralFaceEdges_eq_sdiff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorCentralFaceEdges gamma gamma' =
      rlc_connectorCentralFaceClosureEdges gamma gamma' \
        rlc_connectorFourTraceEdges gamma gamma' := rfl

theorem rlc_connectorCentralFaceEdges_disjoint_fourTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_connectorCentralFaceEdges gamma gamma')
      (rlc_connectorFourTraceEdges gamma gamma') := by
  rw [Finset.disjoint_left]
  intro e heFace heTrace
  exact (Finset.mem_sdiff.mp heFace).2 heTrace

theorem rlc_connectorCentralFaceEdge_endpoints_mem_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈
      rlc_connectorCentralFaceEdges gamma gamma') {z : Site 2}
    (hz : z ∈ e) : z ∈ rlc_connectorBox n := by
  have heClosure := (Finset.mem_sdiff.mp he).1
  have heBox := (Finset.mem_filter.mp heClosure).1
  rw [mem_edgesWithinFinset] at heBox
  obtain ⟨x, hx, y, hy, hxy⟩ := heBox
  subst e
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy

theorem rlc_connectorCentralFaceClosureEdge_endpoints_mem_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈
      rlc_connectorCentralFaceClosureEdges gamma gamma') {z : Site 2}
    (hz : z ∈ e) : z ∈ rlc_connectorBox n := by
  have heBox := (Finset.mem_filter.mp he).1
  rw [mem_edgesWithinFinset] at heBox
  obtain ⟨x, hx, y, hy, hxy⟩ := heBox
  subst e
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy



theorem rlc_connectorCentralFacePlanarEdge_endpoints_mem_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e) : z ∈ rlc_connectorBox n := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union] at he
  rcases he with hclosure | htrace
  · exact rlc_connectorCentralFaceClosureEdge_endpoints_mem_box
      gamma gamma' hclosure hz
  · rw [rlc_connectorFourTraceEdges, Finset.mem_union] at htrace
    rcases htrace with hexposed | hreflected
    · induction e using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_exposedPathEdges_endpoints_mem_box
            (gamma := gamma) (gamma' := gamma') (v := x) (w := y) hexposed
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · simpa [rlc_connectorBox] using hends.1
          · simpa [rlc_connectorBox] using hends.2
    · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union] at hreflected
      rcases hreflected with hright | hleft
      · simpa [rlc_connectorBox] using
          rlc_reflectedRightPathEdge_endpoint_mem_box gamma hright hz
      · simpa [rlc_connectorBox] using
          rlc_reflectedLeftPathEdge_endpoint_mem_box gamma' hleft hz




structure RlcBookPositionedTracePair {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) : Prop where
  exposed_disjoint : Disjoint (rlc_pathVertices gamma.1)
    (rlc_pathVertices gamma'.1)
  right_axis_strict : (gamma.1.1 : Site 2) 1 < 0
  left_axis_strict : 0 < (gamma'.1.2.1 : Site 2) 1





structure RlcBookFaithfulTracePair {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) : Prop
    extends RlcBookPositionedTracePair gamma gamma' where
  right_axis_unique : forall {z : Site 2},
    z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 ->
      z = (gamma.1.1 : Site 2)
  left_axis_unique : forall {z : Site 2},
    z ∈ rlc_pathVertices gamma'.1 -> z 0 = 0 ->
      z = (gamma'.1.2.1 : Site 2)





structure RlcBookFaithfulExtremalTracePair {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) : Prop
    extends RlcBookFaithfulTracePair gamma gamma' where
  extremal_realizable :
    (rlc_extremalPairCandidate (gamma, gamma')).Nonempty



theorem RlcBookFaithfulTracePair.right_vertex_strict {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (h : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1)
    (hne : z ≠ (gamma.1.1 : Site 2)) :
    0 < z 0 := by
  have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
  rw [mem_rect] at hzRect
  have hz0 : z 0 ≠ 0 := by
    intro hz0
    exact hne (h.right_axis_unique hz hz0)
  omega



theorem RlcBookFaithfulTracePair.left_vertex_strict {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (h : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma'.1)
    (hne : z ≠ (gamma'.1.2.1 : Site 2)) :
    z 0 < 0 := by
  have hzRect := rlc_pathVertex_mem_rect gamma'.1 hz
  rw [mem_rect] at hzRect
  have hz0 : z 0 ≠ 0 := by
    intro hz0
    exact hne (h.left_axis_unique hz hz0)
  omega



theorem RlcBookFaithfulTracePair.axis_contacts_strict {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (h : RlcBookFaithfulTracePair gamma gamma') :
    (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 := by
  have hright := h.toRlcBookPositionedTracePair.right_axis_strict
  have hleft := h.toRlcBookPositionedTracePair.left_axis_strict
  omega



theorem rlc_traceSplitCounterexample_bookPositioned :
    RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
  constructor
  · rw [Finset.disjoint_left]
    intro z hzR hzL
    rw [rlc_traceSplitCounterexample_right_vertices] at hzR
    rw [rlc_traceSplitCounterexample_left_vertices] at hzL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzR hzL
    rcases hzR with rfl | rfl | rfl | rfl <;> simp_all
  · change (-1 : Int) < 0
    norm_num
  · change (-1 : Int) < 0
    norm_num




theorem rlc_scaleTwoDoubleFailure_not_bookPositioned :
    ¬ RlcBookPositionedTracePair rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  intro h
  have hstrict := h.left_axis_strict
  change 0 < (0 : Int) at hstrict
  omega



theorem rlc_scaleTwo_centralFace_mem_region :
    rlc_connectorCentralFace ∈
      rlc_connectorCentralFaceRegion rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft :=
  rlc_connectorCentralFace_mem_region _ _ (by norm_num)

end

end StatMech.Universality

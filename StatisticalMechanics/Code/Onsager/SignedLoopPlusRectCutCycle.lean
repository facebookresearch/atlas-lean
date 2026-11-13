/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopAnchoredCutInjective
import Code.Onsager.SignedLoopPlusWiredCut
import Code.Onsager.SignedLoopPlusDualRectangle
import Code.Ising.KWDualBijection
import Code.FrontierB.BoxGraphPath
import Code.FrontierA.KacWardStar
import Code.FK.EdgeConfigZ





open Finset SimpleGraph
open scoped symmDiff

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section


def ons_touchingBondToRectEdge (n : Nat) :
    ons_PlusWiredBond 2 n ->
      Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1)) :=
  fun edge => (ons_touchingBondEquivRectDualEdge n edge).1

theorem ons_touchingBondToRectEdge_injective (n : Nat) :
    Function.Injective (ons_touchingBondToRectEdge n) :=
  Subtype.val_injective.comp (ons_touchingBondEquivRectDualEdge n).injective


def ons_plusRectDualCut (n : Nat)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    Finset (Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) :=
  (multibondCut (ons_plusWiredBondEnds 2 n) config.1).map
    ⟨ons_touchingBondToRectEdge n, ons_touchingBondToRectEdge_injective n⟩

theorem ons_plusRectDualCut_subset_edgeFinset (n : Nat)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    ons_plusRectDualCut n config ⊆
      (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset := by
  intro edge hedge
  rw [ons_plusRectDualCut, Finset.mem_map] at hedge
  obtain ⟨typed, _, rfl⟩ := hedge
  exact (ons_touchingBondEquivRectDualEdge n typed).2


def ons_plusDualContourFace (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    Finset (Sym2 (ons_PlusDualFaceVertex n)) :=
  (ons_plusDualContour n tau).attach.map
    ⟨fun edge => ons_plusDualFaceEdgeLift n
        ⟨edge.1, ons_plusDualContour_subset_plusDualFaceEdgeSet n tau edge.1 edge.2⟩,
      by
        intro edge edge' h
        apply Subtype.ext
        have hmap := congrArg (Sym2.map Subtype.val) h
        simpa using hmap⟩

@[simp] theorem ons_plusDualContourFace_map_val (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    (ons_plusDualContourFace n tau).image (Sym2.map Subtype.val) =
      ons_plusDualContour n tau := by
  ext edge
  simp only [ons_plusDualContourFace, Finset.mem_image, Finset.mem_map,
    Finset.mem_attach, true_and]
  constructor
  · rintro ⟨lifted, ⟨source, hsource, rfl⟩, rfl⟩
    simpa using hsource
  · intro hedge
    let source : {edge // edge ∈ ons_plusDualContour n tau} := ⟨edge, hedge⟩
    refine ⟨ons_plusDualFaceEdgeLift n
        ⟨source.1, ons_plusDualContour_subset_plusDualFaceEdgeSet
          n tau source.1 source.2⟩, ?_, ?_⟩
    · exact ⟨source, rfl⟩
    · exact ons_plusDualFaceEdgeLift_map_val n _


theorem ons_plusDualContourFace_isEven (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    IsEvenSubgraph (ons_plusDualContourFace n tau) := by
  intro f
  have hglobal := ons_plusDualContour_isEven n tau f.1
  have hfilter :
      (ons_plusDualContour n tau).filter
          (fun edge => kwg_incidentMod2 f.1 edge) =
        (ons_plusDualContour n tau).filter (fun edge => f.1 ∈ edge) := by
    ext edge
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hedge
    have hedgeLat : edge ∈ (hypercubicLattice 2).edgeSet := by
      exact (ons_plusDualContour_subset_plusDualFaceEdgeSet
        n tau edge hedge).1
    induction edge using Sym2.inductionOn with
    | _ x y =>
        have hxy : x ≠ y :=
          ((SimpleGraph.mem_edgeSet _).mp hedgeLat).ne
        rw [kwg_incidentMod2_mk, Sym2.mem_iff]
        constructor <;> grind
  change Even (incCount (ons_plusDualContourFace n tau) f)
  change Even ((ons_plusDualContourFace n tau).filter (fun edge => f ∈ edge)).card
  change Even ((ons_plusDualContour n tau).filter
    (fun edge => kwg_incidentMod2 f.1 edge)).card at hglobal
  rw [hfilter] at hglobal
  have hcard :
      ((ons_plusDualContourFace n tau).filter (fun edge => f ∈ edge)).card =
        ((ons_plusDualContour n tau).filter (fun edge => f.1 ∈ edge)).card := by
    apply Finset.card_bij (fun edge _ => Sym2.map Subtype.val edge)
    · intro edge hedge
      rw [Finset.mem_filter] at hedge ⊢
      refine ⟨?_, ?_⟩
      · have himage : Sym2.map Subtype.val edge ∈
            (ons_plusDualContourFace n tau).image (Sym2.map Subtype.val) :=
          Finset.mem_image.mpr ⟨edge, hedge.1, rfl⟩
        simpa [ons_plusDualContourFace_map_val] using himage
      · exact (Sym2.mem_map).2 ⟨f, hedge.2, rfl⟩
    · intro a ha b hb hab
      exact Sym2.map.injective Subtype.val_injective hab
    · intro edge hedge
      rw [Finset.mem_filter] at hedge
      have hcontour : edge ∈ ons_plusDualContour n tau := hedge.1
      have hsupp := ons_plusDualContour_subset_plusDualFaceEdgeSet
        n tau edge hcontour
      let source : {edge // edge ∈ ons_plusDualContour n tau} :=
        ⟨edge, hcontour⟩
      let lifted := ons_plusDualFaceEdgeLift n ⟨edge, hsupp⟩
      refine ⟨lifted, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_map.mpr ⟨source, Finset.mem_attach _ _, rfl⟩
        · have hmapped : f.1 ∈ Sym2.map Subtype.val lifted := by
            rw [show Sym2.map Subtype.val lifted = edge by
              exact ons_plusDualFaceEdgeLift_map_val n _]
            exact hedge.2
          rw [Sym2.mem_map] at hmapped
          obtain ⟨g, hg, hgf⟩ := hmapped
          have hgf' : g = f := Subtype.ext hgf
          rwa [hgf'] at hg
      · exact ons_plusDualFaceEdgeLift_map_val n _
  rw [hcard]
  exact hglobal


def ons_plusRectContour (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    Finset (Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) :=
  transportEdges (ons_plusDualFaceEquivRect n) (ons_plusDualContourFace n tau)

theorem ons_plusRectContour_isEven (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    IsEvenSubgraph (ons_plusRectContour n tau) :=
  isEvenSubgraph_transportEdges (ons_plusDualFaceEquivRect n)
    (ons_plusDualContourFace_isEven n tau)

theorem ons_touchingBondToRectEdge_eq_transport (n : Nat)
    (edge : ons_PlusWiredBond 2 n) :
    ons_touchingBondToRectEdge n edge =
      Sym2.map (ons_plusDualFaceEquivRect n)
        (ons_plusDualFaceEdgeLift n
          (ons_touchingBondEquivPlusDualEdge n edge)) := by
  rfl



theorem ons_plusRectDualCut_optionAnchoredEquiv (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    ons_plusRectDualCut n (ons_optionAnchoredEquiv tau) =
      ons_plusRectContour n tau := by
  ext rectEdge
  constructor
  · intro hrect
    rw [ons_plusRectDualCut, Finset.mem_map] at hrect
    obtain ⟨typed, htyped, rfl⟩ := hrect
    have hprimal := (mem_plusWiredCut_iff 2 n tau typed).mp htyped
    have hdual : flankFacesSym typed.1 ∈ ons_plusDualContour n tau := by
      rw [ons_plusDualContour, Finset.mem_image]
      exact ⟨typed.1, hprimal, rfl⟩
    let source : {edge // edge ∈ ons_plusDualContour n tau} :=
      ⟨flankFacesSym typed.1, hdual⟩
    let supported : {edge // edge ∈ ons_plusDualFaceEdgeSet n} :=
      ons_touchingBondEquivPlusDualEdge n typed
    have hsupported : supported.1 = source.1 := rfl
    rw [ons_plusRectContour, transportEdges, Finset.mem_image]
    refine ⟨ons_plusDualFaceEdgeLift n supported, ?_, ?_⟩
    · rw [ons_plusDualContourFace, Finset.mem_map]
      refine ⟨source, Finset.mem_attach _ _, ?_⟩
      exact congrArg (ons_plusDualFaceEdgeLift n) (Subtype.ext hsupported.symm)
    · exact (ons_touchingBondToRectEdge_eq_transport n typed).symm
  · intro hrect
    rw [ons_plusRectContour, transportEdges, Finset.mem_image] at hrect
    obtain ⟨faceEdge, hface, hrectEq⟩ := hrect
    rw [ons_plusDualContourFace, Finset.mem_map] at hface
    obtain ⟨source, _, hsource⟩ := hface
    have hsourceContour : source.1 ∈ ons_plusDualContour n tau := source.2
    unfold ons_plusDualContour at hsourceContour
    rw [Finset.mem_image] at hsourceContour
    obtain ⟨primalEdge, hprimal, hprimalDual⟩ := hsourceContour
    have hbond : primalEdge ∈ bondFinsetTouch 2 n :=
      (Finset.mem_filter.mp hprimal).1
    let typed : ons_PlusWiredBond 2 n := ⟨primalEdge, hbond⟩
    have htyped : typed ∈ multibondCut (ons_plusWiredBondEnds 2 n)
        (ons_optionAnchoredEquiv tau).1 :=
      (mem_plusWiredCut_iff 2 n tau typed).mpr hprimal
    rw [ons_plusRectDualCut, Finset.mem_map]
    refine ⟨typed, htyped, ?_⟩
    change ons_touchingBondToRectEdge n typed = rectEdge
    rw [ons_touchingBondToRectEdge_eq_transport]
    calc
      Sym2.map (ons_plusDualFaceEquivRect n)
          (ons_plusDualFaceEdgeLift n
            (ons_touchingBondEquivPlusDualEdge n typed)) =
          Sym2.map (ons_plusDualFaceEquivRect n) faceEdge := by
            congr 1
            rw [← hsource]
            apply congrArg (ons_plusDualFaceEdgeLift n)
            apply Subtype.ext
            exact hprimalDual
      _ = rectEdge := hrectEq

theorem ons_plusRectDualCut_isEven (n : Nat)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    IsEvenSubgraph (ons_plusRectDualCut n config) := by
  let tau := (ons_optionAnchoredEquiv
    (I := {x // x ∈ box 2 n})).symm config
  rw [show config = ons_optionAnchoredEquiv tau by
    exact ((ons_optionAnchoredEquiv
      (I := {x // x ∈ box 2 n})).apply_symm_apply config).symm,
    ons_plusRectDualCut_optionAnchoredEquiv]
  exact ons_plusRectContour_isEven n tau

theorem ons_multibondSupportGraph_plusWired_adj_some
    (n : Nat) (x y : {z // z ∈ box 2 n})
    (hxy : (StatMech.FK.boxGraph 2 n).Adj x y) :
    (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Adj
      (some x) (some y) := by
  have hlat : (hypercubicLattice 2).Adj x.1 y.1 :=
    (SimpleGraph.comap_adj.mp hxy)
  have hbond : s(x.1, y.1) ∈ bondFinsetTouch 2 n :=
    mk_mem_bondFinsetTouch hlat (Or.inl x.2)
  let edge : ons_PlusWiredBond 2 n := ⟨s(x.1, y.1), hbond⟩
  refine ⟨fun h => hlat.ne (congrArg Subtype.val (Option.some.inj h)), edge, ?_⟩
  have hout : s(edge.1.out.1, edge.1.out.2) = s(x.1, y.1) := by
    exact edge.1.out_eq.trans rfl
  rw [Sym2.eq_iff] at hout
  rcases hout with hout | hout
  · left
    simp [ons_plusWiredBondEnds, ons_plusWiredVertexOfSite,
      hout.1, hout.2, x.2, y.2]
  · right
    simp [ons_plusWiredBondEnds, ons_plusWiredVertexOfSite,
      hout.1, hout.2, x.2, y.2]


def ons_boxToPlusWiredSupportHom (n : Nat) :
    StatMech.FK.boxGraph 2 n →g
      ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n) where
  toFun := some
  map_rel' := by
    intro x y hxy
    exact ons_multibondSupportGraph_plusWired_adj_some n x y hxy

def ons_plusWiredEastSite (n : Nat) : Site 2 := ![(n : Int), 0]

def ons_plusWiredEastOutsideSite (n : Nat) : Site 2 := ![(n : Int) + 1, 0]

theorem ons_plusWiredEastSite_mem_box (n : Nat) :
    ons_plusWiredEastSite n ∈ box 2 n := by
  intro i
  fin_cases i <;> simp [ons_plusWiredEastSite]

theorem ons_plusWiredEastOutsideSite_not_mem_box (n : Nat) :
    ons_plusWiredEastOutsideSite n ∉ box 2 n := by
  intro h
  have h0 := h 0
  simp [ons_plusWiredEastOutsideSite] at h0
  rw [show (↑n : Int) + 1 = (↑(n + 1) : Int) by omega] at h0
  norm_num at h0
  omega

theorem ons_plusWiredEast_adj (n : Nat) :
    (hypercubicLattice 2).Adj
      (ons_plusWiredEastSite n) (ons_plusWiredEastOutsideSite n) := by
  exact latAdj_right (n : Int) 0

theorem ons_multibondSupportGraph_plusWired_root_adj (n : Nat) :
    (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Adj
      none (some ⟨ons_plusWiredEastSite n,
        ons_plusWiredEastSite_mem_box n⟩) := by
  let x : {z // z ∈ box 2 n} :=
    ⟨ons_plusWiredEastSite n, ons_plusWiredEastSite_mem_box n⟩
  let y := ons_plusWiredEastOutsideSite n
  change (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Adj
    none (some x)
  have hlat : (hypercubicLattice 2).Adj x.1 y := ons_plusWiredEast_adj n
  have hbond : s(x.1, y) ∈ bondFinsetTouch 2 n :=
    mk_mem_bondFinsetTouch hlat (Or.inl x.2)
  let edge : ons_PlusWiredBond 2 n := ⟨s(x.1, y), hbond⟩
  refine ⟨by simp, edge, ?_⟩
  have hout : s(edge.1.out.1, edge.1.out.2) = s(x.1, y) := by
    exact edge.1.out_eq.trans rfl
  rw [Sym2.eq_iff] at hout
  have hxmap : ons_plusWiredVertexOfSite 2 n x.1 = some x := by
    simp [ons_plusWiredVertexOfSite, x.2]
  have hy : y ∉ box 2 n := ons_plusWiredEastOutsideSite_not_mem_box n
  have hymap : ons_plusWiredVertexOfSite 2 n y = none := by
    simp [ons_plusWiredVertexOfSite, hy]
  rcases hout with hout | hout
  · right
    simp only [ons_plusWiredBondEnds, hout.1, hout.2, hxmap, hymap]
  · left
    simp only [ons_plusWiredBondEnds, hout.1, hout.2, hxmap, hymap]

theorem ons_multibondSupportGraph_plusWired_connected (n : Nat) :
    (ons_multibondSupportGraph
      (ons_plusWiredBondEnds 2 n)).Connected := by
  constructor
  intro v w
  have hv : (ons_multibondSupportGraph
      (ons_plusWiredBondEnds 2 n)).Reachable v none := by
    cases v with
    | none => exact ⟨.nil⟩
    | some x =>
        apply Reachable.symm
        apply (ons_multibondSupportGraph_plusWired_root_adj n).reachable.trans
        change (ons_multibondSupportGraph
          (ons_plusWiredBondEnds 2 n)).Reachable
            (some ⟨ons_plusWiredEastSite n,
              ons_plusWiredEastSite_mem_box n⟩) (some x)
        exact (StatMech.FrontierB.boxGraph_preconnected 2 n
          ⟨ons_plusWiredEastSite n, ons_plusWiredEastSite_mem_box n⟩ x).map
            (ons_boxToPlusWiredSupportHom n)
  have hw : (ons_multibondSupportGraph
      (ons_plusWiredBondEnds 2 n)).Reachable none w := by
    cases w with
    | none => exact ⟨.nil⟩
    | some x =>
        apply (ons_multibondSupportGraph_plusWired_root_adj n).reachable.trans
        change (ons_multibondSupportGraph
          (ons_plusWiredBondEnds 2 n)).Reachable
            (some ⟨ons_plusWiredEastSite n,
              ons_plusWiredEastSite_mem_box n⟩) (some x)
        exact (StatMech.FrontierB.boxGraph_preconnected 2 n
          ⟨ons_plusWiredEastSite n, ons_plusWiredEastSite_mem_box n⟩ x).map
            (ons_boxToPlusWiredSupportHom n)
  exact hv.trans hw

theorem ons_plusRectDualCut_injective (n : Nat) :
    Function.Injective (ons_plusRectDualCut n) := by
  intro config config' h
  apply multibondCut_anchored_injective_of_connected
    (ons_plusWiredBondEnds 2 n) none
    (ons_multibondSupportGraph_plusWired_connected n)
  apply Finset.map_injective
    ⟨ons_touchingBondToRectEdge n, ons_touchingBondToRectEdge_injective n⟩
  exact h



abbrev ons_RectHorizontalIndex (M N : Nat) := Fin M × Fin (N + 1)
abbrev ons_RectVerticalIndex (M N : Nat) := Fin (M + 1) × Fin N

def ons_rectHorizontalEdge {M N : Nat}
    (index : ons_RectHorizontalIndex M N) :
    Sym2 (ons_RectDualVertex M N) :=
  s((⟨index.1.val, by omega⟩, index.2),
    (⟨index.1.val + 1, by omega⟩, index.2))

def ons_rectVerticalEdge {M N : Nat}
    (index : ons_RectVerticalIndex M N) :
    Sym2 (ons_RectDualVertex M N) :=
  s((index.1, ⟨index.2.val, by omega⟩),
    (index.1, ⟨index.2.val + 1, by omega⟩))

theorem ons_rectHorizontalEdge_injective (M N : Nat) :
    Function.Injective
      (ons_rectHorizontalEdge : ons_RectHorizontalIndex M N ->
        Sym2 (ons_RectDualVertex M N)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  rw [ons_rectHorizontalEdge, ons_rectHorizontalEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.1
    · exact congrArg (fun p : ons_RectDualVertex M N => p.2) h.1
  · have h1 : i.val = i'.val + 1 :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.1
    have h2 : i.val + 1 = i'.val :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.2
    omega

theorem ons_rectVerticalEdge_injective (M N : Nat) :
    Function.Injective
      (ons_rectVerticalEdge : ons_RectVerticalIndex M N ->
        Sym2 (ons_RectDualVertex M N)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  rw [ons_rectVerticalEdge, ons_rectVerticalEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · apply Prod.ext
    · exact congrArg (fun p : ons_RectDualVertex M N => p.1) h.1
    · apply Fin.ext
      exact congrArg (fun p : ons_RectDualVertex M N => p.2.val) h.1
  · have h1 : j.val = j'.val + 1 :=
      congrArg (fun p : ons_RectDualVertex M N => p.2.val) h.1
    have h2 : j.val + 1 = j'.val :=
      congrArg (fun p : ons_RectDualVertex M N => p.2.val) h.2
    omega

def ons_rectHorizontalEdges (M N : Nat) :
    Finset (Sym2 (ons_RectDualVertex M N)) :=
  Finset.univ.map
    ⟨ons_rectHorizontalEdge, ons_rectHorizontalEdge_injective M N⟩

def ons_rectVerticalEdges (M N : Nat) :
    Finset (Sym2 (ons_RectDualVertex M N)) :=
  Finset.univ.map
    ⟨ons_rectVerticalEdge, ons_rectVerticalEdge_injective M N⟩

theorem ons_rectHorizontalEdges_disjoint_verticalEdges (M N : Nat) :
    Disjoint (ons_rectHorizontalEdges M N) (ons_rectVerticalEdges M N) := by
  rw [Finset.disjoint_left]
  intro edge hhor hver
  rw [ons_rectHorizontalEdges, Finset.mem_map] at hhor
  rw [ons_rectVerticalEdges, Finset.mem_map] at hver
  obtain ⟨⟨i, j⟩, _, rfl⟩ := hhor
  obtain ⟨⟨i', j'⟩, _, h⟩ := hver
  change ons_rectVerticalEdge (i', j') = ons_rectHorizontalEdge (i, j) at h
  rw [ons_rectHorizontalEdge, ons_rectVerticalEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · have hx1 : i'.val = i.val :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.1
    have hx2 : i'.val = i.val + 1 :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.2
    omega
  · have hx1 : i'.val = i.val + 1 :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.1
    have hx2 : i'.val = i.val :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.2
    omega

theorem ons_rectDualGraph_edgeFinset_eq (M N : Nat) :
    (ons_rectDualGraph M N).edgeFinset =
      ons_rectHorizontalEdges M N ∪ ons_rectVerticalEdges M N := by
  ext edge
  induction edge using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change ons_rectDualAdj M N u v ↔ _
      rw [Finset.mem_union]
      constructor
      · rintro (⟨hy, hx⟩ | ⟨hx, hy⟩)
        · by_cases huv : u.1.val < v.1.val
          · have hval : v.1.val = u.1.val + 1 := by
              rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt huv)] at hx
              omega
            let i : Fin M := ⟨u.1.val, by omega⟩
            refine Or.inl ?_
            rw [ons_rectHorizontalEdges, Finset.mem_map]
            refine ⟨(i, u.2), Finset.mem_univ _, ?_⟩
            change ons_rectHorizontalEdge (i, u.2) = s(u, v)
            unfold ons_rectHorizontalEdge
            apply Sym2.eq_iff.mpr
            left
            constructor
            · apply Prod.ext
              · exact Fin.ext (by rfl)
              · rfl
            · apply Prod.ext
              · exact Fin.ext (by simpa using hval.symm)
              · exact hy
          · have hvu : v.1.val < u.1.val := by
              have hne : u.1.val ≠ v.1.val := by
                intro h; simp [h] at hx
              omega
            have hval : u.1.val = v.1.val + 1 := by
              rw [Nat.dist_comm,
                Nat.dist_eq_sub_of_le (Nat.le_of_lt hvu)] at hx
              omega
            let i : Fin M := ⟨v.1.val, by omega⟩
            refine Or.inl ?_
            rw [ons_rectHorizontalEdges, Finset.mem_map]
            refine ⟨(i, v.2), Finset.mem_univ _, ?_⟩
            change ons_rectHorizontalEdge (i, v.2) = s(u, v)
            unfold ons_rectHorizontalEdge
            apply Sym2.eq_iff.mpr
            right
            constructor
            · apply Prod.ext
              · exact Fin.ext (by rfl)
              · rfl
            · apply Prod.ext
              · exact Fin.ext (by simpa using hval.symm)
              · exact hy.symm
        · by_cases huv : u.2.val < v.2.val
          · have hval : v.2.val = u.2.val + 1 := by
              rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt huv)] at hy
              omega
            let j : Fin N := ⟨u.2.val, by omega⟩
            refine Or.inr ?_
            rw [ons_rectVerticalEdges, Finset.mem_map]
            refine ⟨(u.1, j), Finset.mem_univ _, ?_⟩
            change ons_rectVerticalEdge (u.1, j) = s(u, v)
            unfold ons_rectVerticalEdge
            apply Sym2.eq_iff.mpr
            left
            constructor
            · apply Prod.ext
              · rfl
              · exact Fin.ext (by rfl)
            · apply Prod.ext
              · exact hx
              · exact Fin.ext (by simpa using hval.symm)
          · have hvu : v.2.val < u.2.val := by
              have hne : u.2.val ≠ v.2.val := by
                intro h; simp [h] at hy
              omega
            have hval : u.2.val = v.2.val + 1 := by
              rw [Nat.dist_comm,
                Nat.dist_eq_sub_of_le (Nat.le_of_lt hvu)] at hy
              omega
            let j : Fin N := ⟨v.2.val, by omega⟩
            refine Or.inr ?_
            rw [ons_rectVerticalEdges, Finset.mem_map]
            refine ⟨(v.1, j), Finset.mem_univ _, ?_⟩
            change ons_rectVerticalEdge (v.1, j) = s(u, v)
            unfold ons_rectVerticalEdge
            apply Sym2.eq_iff.mpr
            right
            constructor
            · apply Prod.ext
              · rfl
              · exact Fin.ext (by rfl)
            · apply Prod.ext
              · exact hx.symm
              · exact Fin.ext (by simpa using hval.symm)
      · rintro (hhor | hver)
        · rw [ons_rectHorizontalEdges, Finset.mem_map] at hhor
          obtain ⟨⟨i, j⟩, _, h⟩ := hhor
          change ons_rectHorizontalEdge (i, j) = s(u, v) at h
          rw [ons_rectHorizontalEdge, Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [ons_rectDualAdj, Nat.dist_eq_sub_of_le, Nat.dist_comm]
        · rw [ons_rectVerticalEdges, Finset.mem_map] at hver
          obtain ⟨⟨i, j⟩, _, h⟩ := hver
          change ons_rectVerticalEdge (i, j) = s(u, v) at h
          rw [ons_rectVerticalEdge, Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [ons_rectDualAdj, Nat.dist_eq_sub_of_le, Nat.dist_comm]

theorem ons_rectDualGraph_card_edgeFinset (M N : Nat) :
    (ons_rectDualGraph M N).edgeFinset.card =
      M * (N + 1) + (M + 1) * N := by
  rw [ons_rectDualGraph_edgeFinset_eq,
    Finset.card_union_of_disjoint
      (ons_rectHorizontalEdges_disjoint_verticalEdges M N)]
  simp [ons_rectHorizontalEdges, ons_rectVerticalEdges]

theorem ons_rectDualGraph_eq_boxProd_pathGraph (M N : Nat) :
    ons_rectDualGraph M N =
      SimpleGraph.pathGraph (M + 1) □ SimpleGraph.pathGraph (N + 1) := by
  ext u v
  simp only [ons_rectDualGraph, SimpleGraph.boxProd_adj,
    SimpleGraph.pathGraph_adj]
  unfold ons_rectDualAdj
  constructor
  · rintro (⟨hy, hx⟩ | ⟨hx, hy⟩)
    · left
      refine ⟨?_, hy⟩
      by_cases hle : u.1.val ≤ v.1.val
      · rw [Nat.dist_eq_sub_of_le hle] at hx
        omega
      · right
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle))] at hx
        omega
    · right
      refine ⟨?_, hx⟩
      by_cases hle : u.2.val ≤ v.2.val
      · rw [Nat.dist_eq_sub_of_le hle] at hy
        omega
      · right
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle))] at hy
        omega
  · rintro (⟨huv | hvu, hy⟩ | ⟨huv | hvu, hx⟩)
    · left
      refine ⟨hy, ?_⟩
      rw [Nat.dist_eq_sub_of_le (by omega)]
      omega
    · left
      refine ⟨hy, ?_⟩
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]
      omega
    · right
      refine ⟨hx, ?_⟩
      rw [Nat.dist_eq_sub_of_le (by omega)]
      omega
    · right
      refine ⟨hx, ?_⟩
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]
      omega

theorem ons_rectDualGraph_connected (M N : Nat) :
    (ons_rectDualGraph M N).Connected := by
  rw [ons_rectDualGraph_eq_boxProd_pathGraph]
  exact (SimpleGraph.pathGraph_connected M).boxProd
    (SimpleGraph.pathGraph_connected N)



theorem evenSubgraphs_sdiff_tree_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hT : T.IsAcyclic) :
    Set.InjOn (fun F : Finset (Sym2 V) => F \ T.edgeFinset)
      (evenSubgraphs G : Set (Finset (Sym2 V))) := by
  intro A hA B hB heq
  change A \ T.edgeFinset = B \ T.edgeFinset at heq
  have hAdata : A ⊆ G.edgeFinset ∧ IsEvenSubgraph A := by
    simpa [evenSubgraphs] using hA
  have hBdata : B ⊆ G.edgeFinset ∧ IsEvenSubgraph B := by
    simpa [evenSubgraphs] using hB
  let D := A ∆ B
  have hDeven : IsEvenSubgraph D :=
    isEvenSubgraph_symmDiff hAdata.2 hBdata.2
  have hDsub : D ⊆ T.edgeFinset := by
    intro edge hedge
    rw [Finset.mem_symmDiff] at hedge
    by_contra hedgeT
    rcases hedge with hedge | hedge
    · have hleft : edge ∈ A \ T.edgeFinset :=
        Finset.mem_sdiff.mpr ⟨hedge.1, hedgeT⟩
      rw [heq, Finset.mem_sdiff] at hleft
      exact hedge.2 hleft.1
    · have hright : edge ∈ B \ T.edgeFinset :=
        Finset.mem_sdiff.mpr ⟨hedge.1, hedgeT⟩
      rw [← heq, Finset.mem_sdiff] at hright
      exact hedge.2 hright.1
  have hDempty : D = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨edge, hedge⟩
    have hnoDiag : ∀ e ∈ D, ¬ e.IsDiag := by
      intro e he
      have heT : e ∈ T.edgeSet := by
        rw [← SimpleGraph.mem_edgeFinset]
        exact hDsub he
      exact T.not_isDiag_of_mem_edgeSet heT
    have hle : subgraphF D ≤ T := by
      intro a b hab
      rw [subgraphF_adj] at hab
      have heT : s(a, b) ∈ T.edgeFinset := hDsub hab.1
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heT
      exact heT
    have hac : (subgraphF D).IsAcyclic := hT.anti hle
    have hne : (subgraphF D).edgeSet.Nonempty :=
      ⟨edge, (mem_edgeSet_subgraphF D hnoDiag edge).mpr hedge⟩
    exact (StatMech.Lattice.jvp_not_isAcyclic_of_even_nonempty
      (subgraphF D) (subgraphF_even D hnoDiag hDeven) hne) hac
  ext edge
  have hnot : edge ∉ D := by rw [hDempty]; simp
  change edge ∉ A ∆ B at hnot
  rw [Finset.mem_symmDiff] at hnot
  tauto

theorem card_evenSubgraphs_le_spanningTree_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hT : T.IsAcyclic) :
    (evenSubgraphs G).card ≤ 2 ^ (G.edgeFinset \ T.edgeFinset).card := by
  let restrict := fun F : Finset (Sym2 V) => F \ T.edgeFinset
  have hinj : Set.InjOn restrict
      (evenSubgraphs G : Set (Finset (Sym2 V))) :=
    evenSubgraphs_sdiff_tree_injOn G T hT
  have hsubset : (evenSubgraphs G).image restrict ⊆
      (G.edgeFinset \ T.edgeFinset).powerset := by
    intro F hF
    rw [Finset.mem_image] at hF
    obtain ⟨A, hA, rfl⟩ := hF
    rw [Finset.mem_powerset]
    have hAsub : A ⊆ G.edgeFinset := by
      rw [evenSubgraphs, Finset.mem_filter,
        Finset.mem_powerset] at hA
      exact hA.1
    exact Finset.sdiff_subset_sdiff hAsub (Finset.Subset.rfl)
  calc
    (evenSubgraphs G).card = ((evenSubgraphs G).image restrict).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((G.edgeFinset \ T.edgeFinset).powerset).card :=
      Finset.card_le_card hsubset
    _ = 2 ^ (G.edgeFinset \ T.edgeFinset).card :=
      Finset.card_powerset _

noncomputable def ons_rectDualSpanningTree (M N : Nat) :
    SimpleGraph (ons_RectDualVertex M N) :=
  Classical.choose (ons_rectDualGraph_connected M N).exists_isTree_le

theorem ons_rectDualSpanningTree_le (M N : Nat) :
    ons_rectDualSpanningTree M N ≤ ons_rectDualGraph M N :=
  (Classical.choose_spec
    (ons_rectDualGraph_connected M N).exists_isTree_le).1

theorem ons_rectDualSpanningTree_isTree (M N : Nat) :
    (ons_rectDualSpanningTree M N).IsTree :=
  (Classical.choose_spec
    (ons_rectDualGraph_connected M N).exists_isTree_le).2

noncomputable instance ons_rectDualSpanningTree_decidableAdj (M N : Nat) :
    DecidableRel (ons_rectDualSpanningTree M N).Adj := Classical.decRel _

theorem ons_rectDualSpanningTree_complement_card (n : Nat) :
    ((ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset \
      (ons_rectDualSpanningTree (2 * n + 1) (2 * n + 1)).edgeFinset).card =
        (2 * n + 1) ^ 2 := by
  let k := 2 * n + 1
  let G := ons_rectDualGraph k k
  let T := ons_rectDualSpanningTree k k
  have hsub : T.edgeFinset ⊆ G.edgeFinset := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ a b =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge ⊢
        exact ons_rectDualSpanningTree_le k k hedge
  have htree : T.edgeFinset.card + 1 = (k + 1) * (k + 1) := by
    calc
      T.edgeFinset.card + 1 =
          Fintype.card (ons_RectDualVertex k k) :=
        (ons_rectDualSpanningTree_isTree k k).card_edgeFinset
      _ = (k + 1) * (k + 1) := by simp [ons_RectDualVertex]
  have hedge : G.edgeFinset.card = 2 * k * (k + 1) := by
    rw [ons_rectDualGraph_card_edgeFinset]
    ring
  have hid : 2 * k * (k + 1) + 1 =
      (k + 1) * (k + 1) + k ^ 2 := by ring
  change (G.edgeFinset \ T.edgeFinset).card = k ^ 2
  rw [Finset.card_sdiff_of_subset hsub, hedge]
  omega


abbrev ons_PlusRectEvenSubgraph (n : Nat) :=
  {F : Finset (Sym2
      (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) //
    F ∈ evenSubgraphs
      (ons_rectDualGraph (2 * n + 1) (2 * n + 1))}


def ons_plusRectCutEven (n : Nat)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    ons_PlusRectEvenSubgraph n :=
  ⟨ons_plusRectDualCut n config, by
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨ons_plusRectDualCut_subset_edgeFinset n config,
      ons_plusRectDualCut_isEven n config⟩⟩

theorem ons_plusRectCutEven_injective (n : Nat) :
    Function.Injective (ons_plusRectCutEven n) := by
  intro config config' h
  apply ons_plusRectDualCut_injective n
  exact congrArg Subtype.val h

theorem card_ons_plusAnchoredConfig (n : Nat) :
    Fintype.card (AnchoredConfig (ons_PlusWiredVertex 2 n) none) =
      2 ^ ((2 * n + 1) ^ 2) := by
  calc
    Fintype.card (AnchoredConfig (ons_PlusWiredVertex 2 n) none) =
        Fintype.card ({x // x ∈ box 2 n} -> Bool) :=
      (Fintype.card_congr
        (ons_optionAnchoredEquiv
          (I := {x // x ∈ box 2 n}))).symm
    _ = 2 ^ Fintype.card {x // x ∈ box 2 n} := by
      rw [Fintype.card_fun]
      norm_num
    _ = 2 ^ ((2 * n + 1) ^ 2) := by
      rw [StatMech.FK.ecz_boxVerts_card]

theorem card_ons_plusRectEvenSubgraph_le (n : Nat) :
    Fintype.card (ons_PlusRectEvenSubgraph n) ≤
      2 ^ ((2 * n + 1) ^ 2) := by
  let G := ons_rectDualGraph (2 * n + 1) (2 * n + 1)
  let T := ons_rectDualSpanningTree (2 * n + 1) (2 * n + 1)
  have hbound := card_evenSubgraphs_le_spanningTree_complement G T
    (ons_rectDualSpanningTree_isTree
      (2 * n + 1) (2 * n + 1)).isAcyclic
  rw [ons_rectDualSpanningTree_complement_card] at hbound
  rw [show Fintype.card (ons_PlusRectEvenSubgraph n) =
      (evenSubgraphs
        (ons_rectDualGraph (2 * n + 1) (2 * n + 1))).card from
    Fintype.card_coe _]
  simpa [G] using hbound



theorem ons_plusRectCutEven_bijective (n : Nat) :
    Function.Bijective (ons_plusRectCutEven n) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨ons_plusRectCutEven_injective n, ?_⟩
  have hle := Fintype.card_le_of_injective
    (ons_plusRectCutEven n) (ons_plusRectCutEven_injective n)
  have hupper := card_ons_plusRectEvenSubgraph_le n
  rw [card_ons_plusAnchoredConfig] at hle ⊢
  omega

noncomputable def ons_plusRectCutEvenEquiv (n : Nat) :
    AnchoredConfig (ons_PlusWiredVertex 2 n) none ≃
      ons_PlusRectEvenSubgraph n :=
  Equiv.ofBijective (ons_plusRectCutEven n)
    (ons_plusRectCutEven_bijective n)

theorem existsUnique_ons_plusRectDualCut_eq (n : Nat)
    (F : ons_PlusRectEvenSubgraph n) :
    ∃! config : AnchoredConfig (ons_PlusWiredVertex 2 n) none,
      ons_plusRectDualCut n config = F.1 := by
  let config := (ons_plusRectCutEvenEquiv n).symm F
  refine ⟨config, ?_, ?_⟩
  · exact congrArg Subtype.val
      ((ons_plusRectCutEvenEquiv n).apply_symm_apply F)
  · intro other hother
    apply ons_plusRectDualCut_injective n
    exact hother.trans (congrArg Subtype.val
      ((ons_plusRectCutEvenEquiv n).apply_symm_apply F)).symm





def ons_plusRectPathEdgeSign (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v)
    (edge : Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) : Real :=
  if hedge : edge ∈
      (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset then
    (-1 : Real) ^ path.edges.countP (fun primal =>
      decide (primal =
        ((ons_touchingBondEquivRectDualEdge n).symm ⟨edge, hedge⟩).1))
  else 1


def ons_plusRectPathDefectSign (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v)
    (F : ons_PlusRectEvenSubgraph n) : Real :=
  ∏ edge ∈ F.1, ons_plusRectPathEdgeSign n path edge

private theorem ons_sum_countEq_eq_countP {A : Type*} [DecidableEq A]
    (F : Finset A) (l : List A) :
    (∑ e ∈ F, l.countP (fun a => decide (a = e))) =
      l.countP (fun a => decide (a ∈ F)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.countP_cons]
      simp_rw [List.countP_cons]
      rw [Finset.sum_add_distrib, ih]
      by_cases ha : a ∈ F <;> simp [ha]

theorem ons_plusRectPathDefectSign_cut (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    ons_plusRectPathDefectSign n path (ons_plusRectCutEven n config) =
      (-1 : Real) ^ path.edges.countP (fun primal =>
        decide (primal ∈
          (multibondCut (ons_plusWiredBondEnds 2 n) config.1).map
            ⟨Subtype.val, Subtype.val_injective⟩)) := by
  unfold ons_plusRectPathDefectSign ons_plusRectCutEven
  change (∏ edge ∈ ons_plusRectDualCut n config,
      ons_plusRectPathEdgeSign n path edge) = _
  rw [ons_plusRectDualCut, Finset.prod_map]
  calc
    (∏ typed ∈ multibondCut (ons_plusWiredBondEnds 2 n) config.1,
        ons_plusRectPathEdgeSign n path
          (ons_touchingBondToRectEdge n typed)) =
        ∏ typed ∈ multibondCut (ons_plusWiredBondEnds 2 n) config.1,
          (-1 : Real) ^ path.edges.countP
            (fun primal => decide (primal = typed.1)) := by
      apply Finset.prod_congr rfl
      intro typed _
      unfold ons_plusRectPathEdgeSign
      split
      · have hedgeEq :
            (⟨ons_touchingBondToRectEdge n typed, ‹_›⟩ :
              {edge // edge ∈
                (ons_rectDualGraph (2 * n + 1)
                  (2 * n + 1)).edgeFinset}) =
              ons_touchingBondEquivRectDualEdge n typed :=
          Subtype.ext rfl
        rw [hedgeEq, (ons_touchingBondEquivRectDualEdge n).symm_apply_apply]
      · exact False.elim (by
          apply ‹ons_touchingBondToRectEdge n typed ∉ _›
          exact (ons_touchingBondEquivRectDualEdge n typed).2)
    _ = ∏ primal ∈
          (multibondCut (ons_plusWiredBondEnds 2 n) config.1).map
            ⟨Subtype.val, Subtype.val_injective⟩,
        (-1 : Real) ^ path.edges.countP
          (fun edge => decide (edge = primal)) := by
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro typed _
      rfl
    _ = (-1 : Real) ^
        (∑ primal ∈
          (multibondCut (ons_plusWiredBondEnds 2 n) config.1).map
            ⟨Subtype.val, Subtype.val_injective⟩,
          path.edges.countP (fun edge => decide (edge = primal))) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = _ := by
      congr 1
      exact ons_sum_countEq_eq_countP _ path.edges

theorem ons_plusPath_crossCount_eq_wiredCutLattice (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    kwd_crossCount (kwd_sideBoundary (glue (plusField 2) tau)) path =
      path.edges.countP (fun edge =>
        decide (edge ∈ ons_plusWiredCutLattice 2 n tau)) := by
  unfold kwd_crossCount
  apply List.countP_congr
  intro edge hedge
  induction edge using Sym2.inductionOn with
  | _ x y =>
      have hadj : (hypercubicLattice 2).Adj x y :=
        path.adj_of_mem_edges hedge
      let config := glue (plusField 2) tau
      have htouch (hne : config x ≠ config y) :
          x ∈ box 2 n ∨ y ∈ box 2 n := by
        by_contra hnot
        push Not at hnot
        have hx : config x = true := by
          change glue (plusField 2) tau x = true
          rw [glue_not_mem _ _ hnot.1]
          rfl
        have hy : config y = true := by
          change glue (plusField 2) tau y = true
          rw [glue_not_mem _ _ hnot.2]
          rfl
        exact hne (hx.trans hy.symm)
      have hmem : s(x, y) ∈
          ons_fvCutEdges (bondFinsetTouch 2 n) config ↔
          config x ≠ config y := by
        unfold ons_fvCutEdges
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨_, hneg⟩
          exact (kwg_isSplit_mk config x y).mp
            ((kwg_isSplit_iff_bond_neg config s(x, y)).mpr hneg)
        · intro hne
          refine ⟨mk_mem_bondFinsetTouch hadj (htouch hne), ?_⟩
          exact (kwg_isSplit_iff_bond_neg config s(x, y)).mp
            ((kwg_isSplit_mk config x y).mpr hne)
      rw [ons_plusWiredCutLattice_eq_fvCutEdges]
      change kwd_sideBoundary config s(x, y) = true ↔ decide
        (s(x, y) ∈ ons_fvCutEdges (bondFinsetTouch 2 n) config) = true
      have hdecide : decide
          (s(x, y) ∈ ons_fvCutEdges (bondFinsetTouch 2 n) config) =
          decide (config x ≠ config y) := decide_eq_decide.mpr hmem
      rw [kwd_sideBoundary_mk, hdecide]
      cases config x <;> cases config y <;> rfl



theorem ons_plusRectPathDefectSign_optionAnchoredEquiv (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    ons_plusRectPathDefectSign n path
        (ons_plusRectCutEven n (ons_optionAnchoredEquiv tau)) =
      ons_plusWiredEndpointSign 2 n
        (ons_optionAnchoredEquiv tau).1 u v := by
  rw [ons_plusRectPathDefectSign_cut]
  change (-1 : Real) ^ path.edges.countP (fun primal =>
      decide (primal ∈ ons_plusWiredCutLattice 2 n tau)) = _
  rw [← ons_plusPath_crossCount_eq_wiredCutLattice n tau path]
  rw [ons_plusWiredEndpointSign_eq_pathSign 2 n tau path]
  unfold ons_plusLowTempPathSign
  exact (neg_one_pow_eq_ite : (-1 : Real) ^ _ = _)



theorem ons_plusRectPathDefectSign_eq_endpointSign (n : Nat)
    (F : ons_PlusRectEvenSubgraph n) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    ons_plusRectPathDefectSign n path F =
      ons_plusWiredEndpointSign 2 n
        ((ons_plusRectCutEvenEquiv n).symm F).1 u v := by
  let config := (ons_plusRectCutEvenEquiv n).symm F
  let tau := (ons_optionAnchoredEquiv
    (I := {x // x ∈ box 2 n})).symm config
  have hconfig : ons_optionAnchoredEquiv tau = config :=
    (ons_optionAnchoredEquiv
      (I := {x // x ∈ box 2 n})).apply_symm_apply config
  have hF : ons_plusRectCutEven n config = F :=
    (ons_plusRectCutEvenEquiv n).apply_symm_apply F
  calc
    ons_plusRectPathDefectSign n path F =
        ons_plusRectPathDefectSign n path (ons_plusRectCutEven n config) :=
      congrArg (ons_plusRectPathDefectSign n path) hF.symm
    _ = ons_plusWiredEndpointSign 2 n
        (ons_optionAnchoredEquiv tau).1 u v :=
      by
        rw [← hconfig]
        exact ons_plusRectPathDefectSign_optionAnchoredEquiv n tau path
    _ = ons_plusWiredEndpointSign 2 n config.1 u v := by rw [hconfig]
    _ = ons_plusWiredEndpointSign 2 n
        ((ons_plusRectCutEvenEquiv n).symm F).1 u v := by rfl

end

end StatMech.Onsager

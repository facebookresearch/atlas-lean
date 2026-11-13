/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedWideEndpoint



open Set

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section





def fkRectWideTallFinset (n : Int) : Finset (Site 2) :=
  (rect_finite 0 n 0 (3 * n)).toFinset




def fkRectWideExteriorOpenExtension (n : Int)
    (eta : ConfigSpace (Sym2 (Site 2))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ StatMech.Percolation.edgesWithinFinset
      (fkRectWideTallFinset n) then
    StatMech.Universality.crf_swapConfig eta e
  else true

theorem fkRectWideExteriorOpenExtension_eq_swap_of_mem
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2)))
    {e : Sym2 (Site 2)}
    (he : e ∈ StatMech.Percolation.edgesWithinFinset
      (fkRectWideTallFinset n)) :
    fkRectWideExteriorOpenExtension n eta e =
      StatMech.Universality.crf_swapConfig eta e := by
  simp [fkRectWideExteriorOpenExtension, he]



noncomputable def fkRectWideExteriorOpenExtensionToSwapHom
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 (fkRectWideExteriorOpenExtension n eta)
        (rect 0 n 0 (3 * n)) →g
      openSubgraphInduce 2 (StatMech.Universality.crf_swapConfig eta)
        (rect 0 n 0 (3 * n)) where
  toFun z := ⟨z.1, z.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    refine ⟨hxy.1, ?_⟩
    have hx : (x : Site 2) ∈ fkRectWideTallFinset n := by
      simpa [fkRectWideTallFinset] using x.2
    have hy : (y : Site 2) ∈ fkRectWideTallFinset n := by
      simpa [fkRectWideTallFinset] using y.2
    have he : s((x : Site 2), (y : Site 2)) ∈
        StatMech.Percolation.edgesWithinFinset
          (fkRectWideTallFinset n) := by
      rw [StatMech.Percolation.mem_edgesWithinFinset]
      exact ⟨x, hx, y, hy, rfl⟩
    rw [fkRectWideExteriorOpenExtension_eq_swap_of_mem n eta he] at hxy
    change StatMech.Universality.crf_swapConfig eta
      s((x : Site 2), (y : Site 2)) = true
    exact hxy.2




theorem fkRectWideExteriorOpenExtension_not_horizontal
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    ¬ HorizontalCrossing (fkRectWideExteriorOpenExtension n eta)
      0 (3 * n) 0 (3 * n) := by
  intro hwide
  have hnarrow : HorizontalCrossing
      (fkRectWideExteriorOpenExtension n eta) 0 n 0 (3 * n) :=
    StatMech.Universality.bxa_horizontalCrossing_mono_width
      hn (by omega) hwide
  obtain ⟨x, y, hxy⟩ := hnarrow
  have hswap : HorizontalCrossing
      (StatMech.Universality.crf_swapConfig eta) 0 n 0 (3 * n) := by
    refine ⟨⟨x.1, x.2⟩, ⟨y.1, y.2⟩, ?_⟩
    exact hxy.map (fkRectWideExteriorOpenExtensionToSwapHom n eta)
  exact hno (StatMech.Universality.crf_horizontal_to_vertical
    0 (3 * n) 0 n eta hswap)



theorem fkRectWide_faceDualExtension_sharedPrimalEdge_mem
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
    sharedPrimalEdge f g ∈ StatMech.Percolation.edgesWithinFinset
      (fkRectWideTallFinset n) := by
  rw [openSubgraph_adj] at hfg
  obtain ⟨hadj, hopen⟩ := hfg
  rw [StatMech.Universality.fci_faceDualConfig,
    StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hadj] at hopen
  by_contra he
  simp [fkRectWideExteriorOpenExtension, he] at hopen

theorem fkRectWide_endpoint_mem_tall_of_edge_mem
    (n : Int) {e : Sym2 (Site 2)}
    (he : e ∈ StatMech.Percolation.edgesWithinFinset
      (fkRectWideTallFinset n)) {z : Site 2} (hz : z ∈ e) :
    z ∈ fkRectWideTallFinset n := by
  rw [StatMech.Percolation.mem_edgesWithinFinset] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy



theorem fkRectWide_faceDualExtension_adj_fst_le
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
    f 0 ≤ n ∧ g 0 ≤ n := by
  have he := fkRectWide_faceDualExtension_sharedPrimalEdge_mem n eta hfg
  have hf : f = ![f 0, f 1] := by
    funext i
    fin_cases i <;> simp
  rw [hf] at hfg he ⊢
  rcases StatMech.Universality.crr_face_nbr_cases
      (f 0) (f 1) g hfg.1 with hg | hg | hg | hg <;> subst g
  · have hz := fkRectWide_endpoint_mem_tall_of_edge_mem n he
        (show faceCorner10 (f 0) (f 1) ∈
          sharedPrimalEdge ![f 0, f 1] ![f 0 + 1, f 1] by
            rw [sharedPrimalEdge_right]
            simp)
    have hz' : f 0 + 1 ≤ n := by
      have := (show faceCorner10 (f 0) (f 1) ∈
        (rect 0 n 0 (3 * n) : Set (Site 2)) by
          simpa [fkRectWideTallFinset] using hz)
      simpa [faceCorner10, mem_rect] using this.2.1
    simp only [Matrix.cons_val_zero]
    omega
  · have hz := fkRectWide_endpoint_mem_tall_of_edge_mem n he
        (show faceCorner00 (f 0) (f 1) ∈
          sharedPrimalEdge ![f 0, f 1] ![f 0 - 1, f 1] by
            rw [sharedPrimalEdge_left]
            simp)
    have hz' : f 0 ≤ n := by
      have := (show faceCorner00 (f 0) (f 1) ∈
        (rect 0 n 0 (3 * n) : Set (Site 2)) by
          simpa [fkRectWideTallFinset] using hz)
      simpa [faceCorner00, mem_rect] using this.2.1
    simp only [Matrix.cons_val_zero]
    omega
  · have hz := fkRectWide_endpoint_mem_tall_of_edge_mem n he
        (show faceCorner01 (f 0) (f 1) ∈
          sharedPrimalEdge ![f 0, f 1] ![f 0, f 1 + 1] by
            rw [sharedPrimalEdge_top]
            simp)
    have hz' : f 0 ≤ n := by
      have := (show faceCorner01 (f 0) (f 1) ∈
        (rect 0 n 0 (3 * n) : Set (Site 2)) by
          simpa [fkRectWideTallFinset] using hz)
      simpa [faceCorner01, mem_rect] using this.2.1
    simp only [Matrix.cons_val_zero]
    exact ⟨hz', hz'⟩
  · have hz := fkRectWide_endpoint_mem_tall_of_edge_mem n he
        (show faceCorner00 (f 0) (f 1) ∈
          sharedPrimalEdge ![f 0, f 1] ![f 0, f 1 - 1] by
            rw [sharedPrimalEdge_bottom]
            simp)
    have hz' : f 0 ≤ n := by
      have := (show faceCorner00 (f 0) (f 1) ∈
        (rect 0 n 0 (3 * n) : Set (Site 2)) by
          simpa [fkRectWideTallFinset] using hz)
      simpa [faceCorner00, mem_rect] using this.2.1
    simp only [Matrix.cons_val_zero]
    exact ⟨hz', hz'⟩


theorem fkRectWide_faceDualExtension_vertical_band
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    VerticalCrossing
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))
      0 (3 * n - 1) (-1) (3 * n) := by
  exact StatMech.Universality.crr_square_compl_subset_faceDualRect_unconditional
    (3 * n) (by omega)
      (fkRectWideExteriorOpenExtension_not_horizontal n hn eta hno)



theorem fkRectWide_faceDualExtension_vertical_confined
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    VerticalCrossing
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))
      0 n (-1) (3 * n) := by
  let xi := StatMech.Universality.fci_faceDualConfig
    (fkRectWideExteriorOpenExtension n eta)
  obtain ⟨xb, yt, hconn⟩ :=
    fkRectWide_faceDualExtension_vertical_band n hn eta hno
  obtain ⟨w⟩ := hconn
  have hne : (xb : Site 2) ≠ (yt : Site 2) := by
    intro heq
    have hcoord := congrFun heq 1
    have hxb : (xb : Site 2) 1 = -1 := xb.2.2
    have hyt : (yt : Site 2) 1 = 3 * n := yt.2.2
    omega
  have hnonnil : ¬ w.Nil := SimpleGraph.Walk.not_nil_of_ne (by
    intro heq
    exact hne (congrArg Subtype.val heq))
  let emb := SimpleGraph.Embedding.induce (G := openSubgraph 2 xi)
    (rect 0 (3 * n - 1) (-1) (3 * n) : Set (Site 2))
  let p : (openSubgraph 2 xi).Walk (xb : Site 2) (yt : Site 2) :=
    w.map emb.toHom
  have hpsupp : ∀ z ∈ p.support,
      z ∈ (rect 0 n (-1) (3 * n) : Set (Site 2)) := by
    intro z hz
    have hsupp := SimpleGraph.Walk.support_map emb.toHom w
    obtain ⟨z', hz', rfl⟩ := (List.mem_map).mp (hsupp ▸ hz)
    have hzOld := z'.2
    have hzEdge :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
        (p := w) (w := z') hnonnil).mp hz'
    obtain ⟨e, he, hze⟩ := hzEdge
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy := w.adj_of_mem_edges he
        change (openSubgraph 2 xi).Adj (x : Site 2) (y : Site 2) at hxy
        have hle := fkRectWide_faceDualExtension_adj_fst_le n eta hxy
        simp only [Sym2.mem_iff] at hze
        rw [mem_rect] at hzOld ⊢
        rcases hze with rfl | rfl
        · exact ⟨hzOld.1, hle.1, hzOld.2.2.1, hzOld.2.2.2⟩
        · exact ⟨hzOld.1, hle.2, hzOld.2.2.1, hzOld.2.2.2⟩
  have hxbNew : (xb : Site 2) ∈
      (rect 0 n (-1) (3 * n) : Set (Site 2)) :=
    hpsupp _ p.start_mem_support
  have hytNew : (yt : Site 2) ∈
      (rect 0 n (-1) (3 * n) : Set (Site 2)) :=
    hpsupp _ p.end_mem_support
  refine ⟨⟨xb, hxbNew, xb.2.2⟩, ⟨yt, hytNew, yt.2.2⟩, ?_⟩
  exact ⟨p.induce (rect 0 n (-1) (3 * n)) hpsupp⟩



theorem fkRectWide_faceDualExtension_adj_swap
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
    (openSubgraph 2 (StatMech.Universality.fci_faceDualConfig eta)).Adj
      (StatMech.Universality.crf_swap f)
      (StatMech.Universality.crf_swap g) := by
  rw [openSubgraph_adj] at hfg ⊢
  have hadjTarget :=
    (StatMech.Universality.crf_adj_swap f g).mp hfg.1
  refine ⟨hadjTarget, ?_⟩
  rw [StatMech.Universality.fci_faceDualConfig,
    StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hadjTarget]
  have hopen := hfg.2
  rw [StatMech.Universality.fci_faceDualConfig,
    StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hfg.1] at hopen
  have he := fkRectWide_faceDualExtension_sharedPrimalEdge_mem n eta
    (show (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).Adj f g from hfg)
  rw [fkRectWideExteriorOpenExtension_eq_swap_of_mem n eta he,
    StatMech.Universality.crf_swapConfig_apply] at hopen
  have hf : f = ![f 0, f 1] := by
    funext i
    fin_cases i <;> simp
  rw [hf] at hfg hopen ⊢
  rcases StatMech.Universality.crr_face_nbr_cases
      (f 0) (f 1) g hfg.1 with hg | hg | hg | hg <;> subst g
  · simpa [sharedPrimalEdge_right, sharedPrimalEdge_top,
      faceCorner10, faceCorner11, faceCorner01,
      StatMech.Universality.crf_swap,
      StatMech.Universality.crf_swapFun] using hopen
  · simpa [sharedPrimalEdge_left, sharedPrimalEdge_bottom,
      faceCorner00, faceCorner01, faceCorner10,
      StatMech.Universality.crf_swap,
      StatMech.Universality.crf_swapFun] using hopen
  · simpa [sharedPrimalEdge_top, sharedPrimalEdge_right,
      faceCorner01, faceCorner11, faceCorner10,
      StatMech.Universality.crf_swap,
      StatMech.Universality.crf_swapFun] using hopen
  · simpa [sharedPrimalEdge_bottom, sharedPrimalEdge_left,
      faceCorner00, faceCorner10, faceCorner01,
      StatMech.Universality.crf_swap,
      StatMech.Universality.crf_swapFun] using hopen



noncomputable def fkRectWideFaceDualSwapHom
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).induce
          (rect 0 n (-1) (3 * n)) →g
      (openSubgraph 2
        (StatMech.Universality.fci_faceDualConfig eta)).induce
          (rect (-1) (3 * n) 0 n) where
  toFun z := ⟨StatMech.Universality.crf_swap z.1,
    (StatMech.Universality.crf_mem_rect_swap
      0 n (-1) (3 * n) z.1).mp z.2⟩
  map_rel' := by
    intro x y hxy
    exact fkRectWide_faceDualExtension_adj_swap n eta hxy

theorem fkRectWide_faceDualExtension_horizontal_expanded
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    HorizontalCrossing (StatMech.Universality.fci_faceDualConfig eta)
      (-1) (3 * n) 0 n := by
  obtain ⟨xb, yt, hxy⟩ :=
    fkRectWide_faceDualExtension_vertical_confined n hn eta hno
  refine ⟨⟨StatMech.Universality.crf_swap xb.1,
      (StatMech.Universality.crf_mem_bottomSide_swap
        0 n (-1) (3 * n) xb.1).mp xb.2⟩,
    ⟨StatMech.Universality.crf_swap yt.1,
      (StatMech.Universality.crf_mem_topSide_swap
        0 n (-1) (3 * n) yt.1).mp yt.2⟩, ?_⟩
  exact hxy.map (fkRectWideFaceDualSwapHom n eta)



theorem fkRectWide_faceBand_horizontalCrossing_to_rect
    {eta : ConfigSpace (Sym2 (Site 2))} {W H : Int} (hW : 0 < W)
    (h : HorizontalCrossing eta (-1) W 0 H) :
    HorizontalCrossing eta 0 W 0 H := by
  obtain ⟨xl, yr, hconn⟩ := h
  have hxlS : (xl : Site 2) ∈ rect (-1) W 0 H :=
    leftSide_subset xl.2
  have hyrS : (yr : Site 2) ∈ rect (-1) W 0 H :=
    rightSide_subset yr.2
  obtain ⟨w⟩ := hconn
  let p0 : (openSubgraph 2 eta).Walk (xl : Site 2) (yr : Site 2) :=
    w.map (SimpleGraph.Embedding.induce
      (rect (-1) W 0 H : Set (Site 2))).toHom
  let p : (openSubgraph 2 eta).Walk (yr : Site 2) (xl : Site 2) :=
    p0.reverse
  have hpsupp : ∀ z ∈ p.support,
      z ∈ (rect (-1) W 0 H : Set (Site 2)) := by
    intro z hz
    have hz0 : z ∈ p0.support := by simpa [p] using hz
    have hsupp := SimpleGraph.Walk.support_map
      (SimpleGraph.Embedding.induce
        (G := openSubgraph 2 eta)
        (rect (-1) W 0 H : Set (Site 2))).toHom w
    obtain ⟨z', hz', hz'eq⟩ := (List.mem_map).mp (hsupp ▸ hz0)
    rw [← hz'eq]
    exact z'.2
  have hyr0 : (yr : Site 2) 0 = W := yr.2.2
  have hxl0 : (xl : Site 2) 0 = -1 := xl.2.2
  obtain ⟨j, hjle, hju, hjabove⟩ :=
    StatMech.BeffaraDC.torus_walk_first_hit_down p 0 0
      (by omega) (by omega)
  let u : Site 2 := p.getVert j
  let q : (openSubgraph 2 eta).Walk (yr : Site 2) u := p.take j
  have hqsupp : ∀ z ∈ q.support,
      z ∈ (rect 0 W 0 H : Set (Site 2)) := by
    intro z hz
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
    have hzp : z ∈ p.support := List.mem_of_mem_take hz
    have hzS := hpsupp z hzp
    obtain ⟨m, hmlt, hmz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hjp : j ≤ p.length := hjle
    have hzm : z = p.getVert m := by
      have hmplen : m ≤ p.length := hmle.trans hjp
      rw [List.getElem_take] at hmz
      rw [← hmz, ← SimpleGraph.Walk.getVert_eq_support_getElem p hmplen]
    rw [mem_rect] at hzS ⊢
    have hznonneg : 0 ≤ z 0 := by
      rw [hzm]
      rcases lt_or_eq_of_le hmle with hm | rfl
      · exact le_of_lt (hjabove m hm)
      · exact le_of_eq hju.symm
    omega
  have huT : u ∈ (rect 0 W 0 H : Set (Site 2)) :=
    hqsupp u q.end_mem_support
  have hyrT : (yr : Site 2) ∈ (rect 0 W 0 H : Set (Site 2)) :=
    hqsupp _ q.start_mem_support
  have hu0 : u 0 = 0 := hju
  refine ⟨⟨u, huT, hu0⟩, ⟨(yr : Site 2), hyrT, hyr0⟩, ?_⟩
  exact ⟨q.reverse.induce (rect 0 W 0 H) (by
    intro z hz
    exact hqsupp z (by simpa using hz))⟩




theorem fkRectWide_faceDualHorizontal_of_not_vertical
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    HorizontalCrossing (StatMech.Universality.fci_faceDualConfig eta)
      0 (3 * n) 0 n :=
  fkRectWide_faceBand_horizontalCrossing_to_rect (by omega)
    (fkRectWide_faceDualExtension_horizontal_expanded n hn eta hno)



theorem fkRectDevelopedThreeByOneVertex_fst_succ_lt
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
    (fkRectDevelopedSquareVertex R n z).1.val + 1 < R.width := by
  let t := fkRectDevelopedSquarePoint n z
  let p := fkRectSquareUndevelopPoint t
  have hp := fkRectDevelopedThreeByOne_undevelop_bounds
    R n hwidth hheight hz
  have hpoint := fkRectVertexSquarePoint_developedThreeByOneVertex
    R n hwidth hheight hz
  have hundev := congrArg fkRectSquareUndevelopPoint hpoint
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at hundev
  have hx : ((fkRectDevelopedSquareVertex R n z).1.val : Int) = p.1 :=
    congrArg Prod.fst hundev
  change z ∈ rect 0 (3 * (n : Int)) 0 n at hz
  rw [mem_rect] at hz
  have hpUpper : p.1 < 4 * (n : Int) := by
    dsimp [p, t, fkRectDevelopedSquarePoint,
      fkRectSquareUndevelopPoint]
    omega
  exact_mod_cast (show
    ((fkRectDevelopedSquareVertex R n z).1.val : Int) + 1 < R.width by
      omega)



theorem fkRectDualEdgeToEdge_not_cut_of_developedThreeByOne
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {f g : Site 2} (hf : f ∈ fkRectDevelopedThreeByOneRect n)
    (hg : g ∈ fkRectDevelopedThreeByOneRect n)
    (d : R.EdgeIndex)
    (hedge : fkRectTorusIndexedEdge R d =
      s(fkRectDevelopedSquareVertex R n f,
        fkRectDevelopedSquareVertex R n g))
    (hd : d ∉ fkRectTorusCutEdges R) :
    fkRectDualEdgeToEdge R d ∉ fkRectTorusCutEdges R := by
  rcases d with ⟨b, x, y⟩
  cases b
  · have hxy : y.val ≠ 0 ∧ x.val ≠ 0 := by
      simpa [mem_fkRectTorusCutEdges_iff] using hd
    simpa [fkRectDualEdgeToEdge,
      mem_fkRectTorusCutEdges_iff] using hxy.1
  · have hy0 : y.val ≠ 0 := by
      simpa [mem_fkRectTorusCutEdges_iff] using hd
    have hedge' := hedge
    simp only [fkRectTorusIndexedEdge, if_pos] at hedge'
    have hxface : x = (fkRectDevelopedSquareVertex R n f).1 ∨
        x = (fkRectDevelopedSquareVertex R n g).1 := by
      rcases Sym2.eq_iff.mp hedge' with h | h
      · exact Or.inl (congrArg Prod.fst h.1)
      · exact Or.inr (congrArg Prod.fst h.1)
    have hxsucc : x.val + 1 < R.width := by
      rcases hxface with hx | hx
      · rw [hx]
        exact fkRectDevelopedThreeByOneVertex_fst_succ_lt
          R n hn hwidth hheight hf
      · rw [hx]
        exact fkRectDevelopedThreeByOneVertex_fst_succ_lt
          R n hn hwidth hheight hg
    have hsucc : (finitePeriodicSucc R.width_pos x).val = x.val + 1 := by
      rw [finitePeriodicSucc_val]
      simp [ne_of_lt hxsucc]
    rw [mem_fkRectTorusCutEdges_iff]
    simp [fkRectDualEdgeToEdge, hy0, hsucc]



theorem fkRectDevelopedThreeByOne_faceDual_adj_imp_dual_adj
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) {f g : Site 2}
    (hf : f ∈ fkRectDevelopedThreeByOneRect n)
    (hg : g ∈ fkRectDevelopedThreeByOneRect n)
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).Adj f g) :
    (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Adj
      (fkRectDevelopedSquareVertex R n f)
      (fkRectDevelopedSquareVertex R n g) := by
  rw [openSubgraph_adj] at hfg
  obtain ⟨hlat, hopen⟩ := hfg
  have hcut := fkRectDevelopedThreeByOneVertex_cutGraph_adj R n
    hwidth hheight hf hg hlat
  obtain ⟨⟨d, hedge⟩, hcutEdge⟩ :=
    (fkRectCutGraph_adj_iff R _ _).mp hcut
  have hd : d ∉ fkRectTorusCutEdges R := by
    intro hd
    apply hcutEdge
    rw [← hedge, mem_fkRectTorusCutGraphEdges]
    exact hd
  let e := fkRectDualEdgeToEdge R d
  have he : e ∉ fkRectTorusCutEdges R :=
    fkRectDualEdgeToEdge_not_cut_of_developedThreeByOne
      R n hn hwidth hheight hf hg d hedge hd
  have hde : fkRectEdgeToDualEdge R e = d := by
    simp [e]
  let dp := fkRectLiftedIndexedEdgeEnds R d
  let ep := fkRectLiftedIndexedEdgeEnds R e
  have hproject :
      s(fkRectLiftedVertex R dp.1, fkRectLiftedVertex R dp.2) =
        s(fkRectDevelopedSquareVertex R n f,
          fkRectDevelopedSquareVertex R n g) := by
    rw [← fkRectLiftedIndexedEdgeEnds_project R d]
    exact hedge
  have hsites := congrArg (Sym2.map (fkRectVertexSquareSite R)) hproject
  have hd1 :=
    fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut R d hd
  have hd2 :=
    fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut₂ R d hd
  have hsites' :
      s(fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1),
          fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) =
        s(fkRectDevelopedSquareSite n f,
          fkRectDevelopedSquareSite n g) := by
    simp only [Sym2.map_pair_eq] at hsites
    rw [fkRectVertexSquareSite_developedThreeByOneVertex
          R n hwidth hheight hf,
        fkRectVertexSquareSite_developedThreeByOneVertex
          R n hwidth hheight hg] at hsites
    change s(fkRectSquareSiteOfPair
          (fkRectVertexSquarePoint R (fkRectLiftedVertex R dp.1)),
        fkRectSquareSiteOfPair
          (fkRectVertexSquarePoint R (fkRectLiftedVertex R dp.2))) = _ at hsites
    rw [← hd1, ← hd2] at hsites
    exact hsites
  have htadj : (hypercubicLattice 2).Adj
      (fkRectDevelopedSquareSite n f)
      (fkRectDevelopedSquareSite n g) := by
    rw [hypercubicLattice_adj] at hlat ⊢
    simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
      fkRectSquareSiteOfPair, Fin.sum_univ_two] using hlat
  have hshared :
      sharedPrimalEdge (fkRectDevelopedSquareSite n f)
          (fkRectDevelopedSquareSite n g) =
        sharedPrimalEdge
          (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1))
          (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) := by
    rcases Sym2.eq_iff.mp hsites' with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      exact sharedPrimalEdge_comm_of_adj htadj
  have hcross := fkRectLiftedDualEdge_sharedPrimalEdge R e he (by
    simpa [hde] using hd)
  dsimp only at hcross
  rw [hde] at hcross
  change sharedPrimalEdge
      (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1))
      (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) =
    Sym2.map fkRectSquareSiteOfPair
      s(fkRectSquareDevelopPoint ep.1,
        fkRectSquareDevelopPoint ep.2) at hcross
  have hplane := hshared.trans hcross
  have hmapped := congrArg (Sym2.map (fkRectSquareSiteVertex R)) hplane
  rw [fkRectDevelopedSquare_sharedPrimalEdge n hlat] at hmapped
  have hedgeMap :
      Sym2.map (fkRectDevelopedSquareVertex R n)
          (sharedPrimalEdge f g) = fkRectTorusIndexedEdge R e := by
    rw [fkRectLiftedIndexedEdgeEnds_project R e]
    simpa [Sym2.map_map, Function.comp_def,
      fkRectSquareRepresentativeVertex_developPoint, ep] using hmapped
  have hpull : fkRectDevelopedSquarePullback R n omega
      (sharedPrimalEdge f g) = false := by
    rw [StatMech.Universality.fci_faceDualConfig,
      StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hlat] at hopen
    cases hval : fkRectDevelopedSquarePullback R n omega
        (sharedPrimalEdge f g) <;> simp_all
  have heclosed : omega e = false := by
    unfold fkRectDevelopedSquarePullback at hpull
    rw [hedgeMap, fkRectFullGraphConfiguration_indexedEdge] at hpull
    exact hpull
  refine ⟨d, ?_, hedge⟩
  rw [← hde, fkRectDualConfigurationEquiv_apply_edgeToDualEdge]
  simpa [heclosed]



noncomputable def fkRectDevelopedThreeByOneFaceDualToDualPullbackHom
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).induce
          (fkRectDevelopedThreeByOneRect n) →g
      (openSubgraph 2
        (fkRectDevelopedSquarePullback R n
          (fkRectDualConfigurationEquiv R omega))).induce
            (fkRectDevelopedThreeByOneRect n) where
  toFun z := ⟨z.1, z.2⟩
  map_rel' := by
    intro z w hzw
    have htorus := fkRectDevelopedThreeByOne_faceDual_adj_imp_dual_adj
      R n hn hwidth hheight omega z.2 w.2 hzw
    change (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).Adj z.1 w.1 at hzw
    change (openSubgraph 2
      (fkRectDevelopedSquarePullback R n
        (fkRectDualConfigurationEquiv R omega))).Adj z.1 w.1
    rw [openSubgraph_adj] at hzw ⊢
    exact ⟨hzw.1, (fkRectDevelopedThreeByOnePullback_open_iff
      R n hwidth hheight (fkRectDualConfigurationEquiv R omega)
      z.2 w.2 hzw.1).mpr htorus⟩



theorem fkRectDevelopedThreeByOne_faceDual_connectedWithin_imp_dual
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration)
    {x y : fkRectDevelopedThreeByOneRect n}
    (hxy : ConnectedWithin 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))
      (fkRectDevelopedThreeByOneRect n) x y) :
    ConnectedWithin 2
      (fkRectDevelopedSquarePullback R n
        (fkRectDualConfigurationEquiv R omega))
      (fkRectDevelopedThreeByOneRect n) x y := by
  exact hxy.map
    (fkRectDevelopedThreeByOneFaceDualToDualPullbackHom
      R n hn hwidth hheight omega)



def fkRectDevelopedThreeByOneFaceDualHorizontalEvent
    (R : FKRectTorus) (n : Nat) : Set R.Configuration :=
  {omega | HorizontalCrossing
    (StatMech.Universality.fci_faceDualConfig
      (fkRectDevelopedSquarePullback R n omega))
    0 (3 * (n : Int)) 0 n}


theorem fkRectDevelopedThreeByOne_faceDualHorizontal_imp_dualHorizontal
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration)
    (hcross : omega ∈
      fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
    fkRectDualConfigurationEquiv R omega ∈
      fkRectDevelopedRectangleHorizontalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n := by
  obtain ⟨x, y, hxy⟩ := hcross
  refine ⟨x, y, ?_⟩
  change ConnectedWithin 2
    (fkRectDevelopedSquarePullback R n
      (fkRectDualConfigurationEquiv R omega))
    (fkRectDevelopedThreeByOneRect n)
    ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩
  exact fkRectDevelopedThreeByOne_faceDual_connectedWithin_imp_dual
    R n hn hwidth hheight omega (by
      simpa [fkRectDevelopedThreeByOneRect] using hxy)



theorem fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n) :
    (fkRectDevelopedRectangleVerticalCrossingEvent
      R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n := by
  intro omega hno
  exact fkRectWide_faceDualHorizontal_of_not_vertical
    (n : Int) (by omega) (fkRectDevelopedSquarePullback R n omega) hno




theorem fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (hface :
      (fkRectDevelopedRectangleVerticalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
    fkRectDualEvent R
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedRectangleHorizontalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n := by
  rintro eta ⟨omega, hno, rfl⟩
  exact fkRectDevelopedThreeByOne_faceDualHorizontal_imp_dualHorizontal
    R n hn hwidth hheight omega (hface hno)


theorem fkRectDevelopedThreeByOne_dualCompl_subset_horizontal
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height) :
    fkRectDualEvent R
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedRectangleHorizontalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n :=
  fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual
    R n hn hwidth hheight
      (fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal R n hn)



theorem fkRectDevelopedThreeByOne_dualPreimageHorizontalCompl_subset_vertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height) :
    fkRectDualPreimageEvent R
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedRectangleVerticalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n := by
  intro omega hnoHorizontal
  by_contra hnoVertical
  have hdualHorizontal :=
    fkRectDevelopedThreeByOne_dualCompl_subset_horizontal
      R n hn hwidth hheight
      (show fkRectDualConfigurationEquiv R omega ∈
        fkRectDualEvent R
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n)ᶜ from
        ⟨omega, hnoVertical, rfl⟩)
  exact hnoHorizontal hdualHorizontal





theorem fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal_of_faceDual
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q)
    (hface :
      (fkRectDevelopedRectangleVerticalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
    1 ≤
      fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) +
        q ^ 2 * fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) := by
  let V := fkRectDevelopedRectangleVerticalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  let H := fkRectDevelopedRectangleHorizontalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_le_q_mul_dualEvent R hq Vᶜ
  have hmono := fkRectCriticalEventMass_mono R hq0
    (fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual
      R n hn hwidth hheight hface)
  rw [fkRectCriticalEventMass_compl R hq0 V] at hdual
  have hlinear : 1 - fkRectCriticalEventMass R q V ≤
      q * fkRectCriticalEventMass R q H :=
    hdual.trans (mul_le_mul_of_nonneg_left hmono hq0.le)
  have hqSq : q ≤ q ^ 2 := by nlinarith
  have hHnonneg : 0 ≤ fkRectCriticalEventMass R q H :=
    fkRectCriticalEventMass_nonneg R hq0 H
  have hweaken : q * fkRectCriticalEventMass R q H ≤
      q ^ 2 * fkRectCriticalEventMass R q H :=
    mul_le_mul_of_nonneg_right hqSq hHnonneg
  dsimp only [V, H] at hlinear hweaken ⊢
  linarith



theorem fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 ≤
      fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) +
        q ^ 2 * fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) :=
  fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal_of_faceDual
    R n hn hwidth hheight hq
      (fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal R n hn)



theorem fkRectCritical_one_le_threeByOneHorizontal_add_q_sq_mul_vertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 ≤
      fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) +
        q ^ 2 * fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) := by
  let H := fkRectDevelopedRectangleHorizontalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  let V := fkRectDevelopedRectangleVerticalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  let A := fkRectDualPreimageEvent R Hᶜ
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_dualEvent_le R hq A
  have hdualEq : fkRectDualEvent R A = Hᶜ :=
    fkRectDualEvent_dualPreimageEvent R Hᶜ
  rw [hdualEq, fkRectCriticalEventMass_compl R hq0 H] at hdual
  have hmono := fkRectCriticalEventMass_mono R hq0
    (fkRectDevelopedThreeByOne_dualPreimageHorizontalCompl_subset_vertical
      R n hn hwidth hheight)
  have hlinear : 1 - fkRectCriticalEventMass R q H ≤
      q * fkRectCriticalEventMass R q V :=
    hdual.trans (mul_le_mul_of_nonneg_left hmono hq0.le)
  have hqSq : q ≤ q ^ 2 := by nlinarith
  have hV0 : 0 ≤ fkRectCriticalEventMass R q V :=
    fkRectCriticalEventMass_nonneg R hq0 V
  have hweaken : q * fkRectCriticalEventMass R q V ≤
      q ^ 2 * fkRectCriticalEventMass R q V :=
    mul_le_mul_of_nonneg_right hqSq hV0
  dsimp only [H, V] at hlinear hweaken ⊢
  linarith

end

end StatMech.FrontierD

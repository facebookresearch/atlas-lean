/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4OuterLeafDual
import Code.FK.OffCentreDomination
import Code.Lattice.ClusterContourBijection

open Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

private theorem site_mem_box_of_int_bounds {m : Nat} {a b : Int}
    (ha : -(m : Int) ≤ a ∧ a ≤ m) (hb : -(m : Int) ≤ b ∧ b ≤ m) :
    (![a, b] : Site 2) ∈ box 2 m := by
  intro i
  fin_cases i
  · change a.natAbs ≤ m
    rcases Int.natAbs_eq a with h | h <;> omega
  · change b.natAbs ≤ m
    rcases Int.natAbs_eq b with h | h <;> omega



theorem fkSquareBoxPlanar_imageGraph_adj_iff (m : Nat) (x y : Site 2) :
    (imageGraph (fkSquareBoxPlanar m)).Adj x y ↔
      x ∈ box 2 m ∧ y ∈ box 2 m ∧ (hypercubicLattice 2).Adj x y := by
  rw [imageGraph_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨a.2, b.2, hab⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy, rfl, rfl⟩



theorem sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner
    {N m : Nat} (hNm : N < m) {f g : Site 2}
    (hf : f ∈ box 2 N) (hfg : (hypercubicLattice 2).Adj f g) :
    sharedPrimalEdge f g ∈ (imageGraph (fkSquareBoxPlanar m)).edgeSet := by
  have hf0 := hf 0
  have hf1 := hf 1
  have hb0 : -(m : Int) ≤ f 0 ∧ f 0 + 1 ≤ m := by
    rcases Int.natAbs_eq (f 0) with h | h <;> omega
  have hb1 : -(m : Int) ≤ f 1 ∧ f 1 + 1 ≤ m := by
    rcases Int.natAbs_eq (f 1) with h | h <;> omega
  rcases adj_cases hfg with ⟨h0, hfg1 | hgf1⟩ | ⟨h1, hfg0 | hgf0⟩
  · have he : sharedPrimalEdge f g =
        s(![f 0, f 1], ![f 0 + 1, f 1]) := by
      unfold sharedPrimalEdge
      rw [if_pos h0, show max (f 1) (g 1) = f 1 by omega]
    rw [he, SimpleGraph.mem_edgeSet,
      fkSquareBoxPlanar_imageGraph_adj_iff]
    exact ⟨site_mem_box_of_int_bounds
        ⟨hb0.1, by omega⟩ ⟨hb1.1, by omega⟩,
      site_mem_box_of_int_bounds ⟨by omega, hb0.2⟩ ⟨hb1.1, by omega⟩,
      by simpa using latAdj_right (f 0) (f 1)⟩
  · have he : sharedPrimalEdge f g =
        s(![f 0, f 1 + 1], ![f 0 + 1, f 1 + 1]) := by
      unfold sharedPrimalEdge
      rw [if_pos h0, show max (f 1) (g 1) = g 1 by omega]
      congr 1 <;> funext i <;> fin_cases i <;> simp <;> omega
    rw [he, SimpleGraph.mem_edgeSet,
      fkSquareBoxPlanar_imageGraph_adj_iff]
    exact ⟨site_mem_box_of_int_bounds ⟨hb0.1, by omega⟩ ⟨by omega, hb1.2⟩,
      site_mem_box_of_int_bounds ⟨by omega, hb0.2⟩ ⟨by omega, hb1.2⟩,
      by simpa using latAdj_right (f 0) (f 1 + 1)⟩
  · have he : sharedPrimalEdge f g =
        s(![f 0, f 1], ![f 0, f 1 + 1]) := by
      unfold sharedPrimalEdge
      rw [if_neg (by intro h; omega),
        show max (f 0) (g 0) = f 0 by omega]
    rw [he, SimpleGraph.mem_edgeSet,
      fkSquareBoxPlanar_imageGraph_adj_iff]
    exact ⟨site_mem_box_of_int_bounds ⟨hb0.1, by omega⟩ ⟨hb1.1, by omega⟩,
      site_mem_box_of_int_bounds ⟨hb0.1, by omega⟩ ⟨by omega, hb1.2⟩,
      by simpa using latAdj_top (f 0) (f 1)⟩
  · have he : sharedPrimalEdge f g =
        s(![f 0 + 1, f 1], ![f 0 + 1, f 1 + 1]) := by
      unfold sharedPrimalEdge
      rw [if_neg (by intro h; omega),
        show max (f 0) (g 0) = g 0 by omega]
      congr 1 <;> funext i <;> fin_cases i <;> simp <;> omega
    rw [he, SimpleGraph.mem_edgeSet,
      fkSquareBoxPlanar_imageGraph_adj_iff]
    exact ⟨site_mem_box_of_int_bounds ⟨by omega, hb0.2⟩ ⟨hb1.1, by omega⟩,
      site_mem_box_of_int_bounds ⟨by omega, hb0.2⟩ ⟨by omega, hb1.2⟩,
      by simpa using latAdj_top (f 0 + 1) (f 1)⟩



theorem fkSquareBox_innerFace_neighborSet_eq_empty
    {N m : Nat} (hNm : N < m) (f : Site 2) (hf : f ∈ box 2 N) :
    (whb_faceRegion (imageGraph (fkSquareBoxPlanar m))).neighborSet f = ∅ := by
  ext g
  constructor
  · intro hfg
    exact (hfg.2
      (sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner hNm hf hfg.1)).elim
  · simp



theorem pfdFace_eq_inner_iff
    {N m : Nat} (hNm : N < m) {f g : Site 2} (hg : g ∈ box 2 N) :
    pfdFace (fkSquareBoxPlanar m) f = pfdFace (fkSquareBoxPlanar m) g ↔ f = g := by
  constructor
  · intro hface
    have hreach : (whb_faceRegion (imageGraph (fkSquareBoxPlanar m))).Reachable f g :=
      ConnectedComponent.eq.mp hface
    by_contra hne
    exact (not_reachable_of_neighborSet_right_eq_empty hne
      (fkSquareBox_innerFace_neighborSet_eq_empty hNm g hg)) hreach
  · exact fun h => congrArg (pfdFace (fkSquareBoxPlanar m)) h



def fkSquareBox_innerFaceMap (N m : Nat) :
    FK.boxVerts 2 N → kwg_Face (fkSquareBoxPlanar m) :=
  fun x => pfdFace (fkSquareBoxPlanar m) x.1

theorem fkSquareBox_innerFaceMap_injective
    {N m : Nat} (hNm : N < m) :
    Function.Injective (fkSquareBox_innerFaceMap N m) := by
  intro x y hxy
  apply Subtype.ext
  exact (pfdFace_eq_inner_iff hNm y.2).mp hxy


noncomputable def fkSquareBoxFullDualGraph (m : Nat) :
    SimpleGraph (kwg_Face (fkSquareBoxPlanar m)) :=
  pfdClosedDual (fkSquareBoxPlanar m) ⊥

noncomputable instance fkSquareBoxFullDualGraphDecidableRel (m : Nat) :
    DecidableRel (fkSquareBoxFullDualGraph m).Adj := Classical.decRel _



theorem fkSquareBox_innerFaceMap_adj
    {N m : Nat} (hNm : N < m) (x y : FK.boxVerts 2 N) :
    (FK.boxGraph 2 N).Adj x y ↔
      (fkSquareBoxFullDualGraph m).Adj
        (fkSquareBox_innerFaceMap N m x)
        (fkSquareBox_innerFaceMap N m y) := by
  let P := fkSquareBoxPlanar m
  constructor
  · intro hxy
    have hwall : sharedPrimalEdge x.1 y.1 ∈ (imageGraph P).edgeSet :=
      sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner hNm x.2 hxy
    induction hshared : sharedPrimalEdge x.1 y.1 using Sym2.inductionOn with
    | _ a b =>
        have habImage : (imageGraph P).Adj a b := by
          rw [← SimpleGraph.mem_edgeSet]
          exact hshared ▸ hwall
        rw [imageGraph_adj] at habImage
        obtain ⟨u, v, huv, hua, hvb⟩ := habImage
        let e : kwg_Edge P :=
          ⟨s(u, v), (SimpleGraph.mem_edgeSet P.G).mpr huv⟩
        have hemb : kwg_embeddedEdge P e = sharedPrimalEdge x.1 y.1 := by
          rw [hshared, ← hua, ← hvb]
          rfl
        have hflank : s(kwg_flankLeft P e, kwg_flankRight P e) =
            s(x.1, y.1) :=
          (jce_sharedPrimalEdge_inj (kwg_flanks_adj P e) hxy).mpr
            ((kwg_flanks_shared P e).trans hemb)
        have hends : kwg_dualEnds P e =
            s(pfdFace P x.1, pfdFace P y.1) := by
          unfold kwg_dualEnds pfdFace
          exact congrArg
            (Sym2.map
              ((whb_faceRegion (imageGraph P)).connectedComponentMk))
            hflank
        have hne : pfdFace P x.1 ≠ pfdFace P y.1 := by
          intro heq
          exact hxy.ne (Subtype.ext
            ((pfdFace_eq_inner_iff hNm y.2).mp heq))
        rw [fkSquareBoxFullDualGraph, pfdClosedDual_adj]
        exact ⟨hne, e, by simp, hends⟩
  · intro hxy
    rw [fkSquareBoxFullDualGraph, pfdClosedDual_adj] at hxy
    obtain ⟨_, e, _, hends⟩ := hxy
    change s(pfdFace (fkSquareBoxPlanar m) (kwg_flankLeft (fkSquareBoxPlanar m) e),
        pfdFace (fkSquareBoxPlanar m) (kwg_flankRight (fkSquareBoxPlanar m) e)) =
      s(pfdFace (fkSquareBoxPlanar m) x.1,
        pfdFace (fkSquareBoxPlanar m) y.1) at hends
    rw [Sym2.eq_iff] at hends
    rcases hends with hends | hends
    · have hL : kwg_flankLeft (fkSquareBoxPlanar m) e = x.1 :=
        (pfdFace_eq_inner_iff hNm x.2).mp hends.1
      have hR : kwg_flankRight (fkSquareBoxPlanar m) e = y.1 :=
        (pfdFace_eq_inner_iff hNm y.2).mp hends.2
      simpa [hL, hR] using kwg_flanks_adj (fkSquareBoxPlanar m) e
    · have hL : kwg_flankLeft (fkSquareBoxPlanar m) e = y.1 :=
        (pfdFace_eq_inner_iff hNm y.2).mp hends.1
      have hR : kwg_flankRight (fkSquareBoxPlanar m) e = x.1 :=
        (pfdFace_eq_inner_iff hNm x.2).mp hends.2
      exact (by simpa [hL, hR] using
        (kwg_flanks_adj (fkSquareBoxPlanar m) e).symm)



theorem fkSquareBox_innerFaceMap_adjMatch
    {N m : Nat} (hNm : N < m) :
    ocd_AdjMatch (FK.boxGraph 2 N) (fkSquareBoxFullDualGraph m)
      (fkSquareBox_innerFaceMap N m) :=
  fkSquareBox_innerFaceMap_adj hNm



theorem fkSquareBox_boundary_of_outsideGraph_adj
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    (psi : ConfigSpace (Sym2 (kwg_Face (fkSquareBoxPlanar m))))
    {x : FK.boxVerts 2 N} {z : kwg_Face (fkSquareBoxPlanar m)}
    (h : (ocd_outsideGraph (fkSquareBoxFullDualGraph m)
      (fkSquareBox_innerFaceMap N m) (fun _ => False) psi).Adj
        (fkSquareBox_innerFaceMap N m x) z) :
    FK.boxBoundary 2 N x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hxfalse, _⟩
  · rw [FK.boxBoundary, mem_vertexBoundary]
    refine ⟨x.2, ?_⟩
    intro hxinner
    rw [fkSquareBoxFullDualGraph, pfdClosedDual_adj] at hadj
    obtain ⟨_, e, _, hends⟩ := hadj
    change s(pfdFace (fkSquareBoxPlanar m)
        (kwg_flankLeft (fkSquareBoxPlanar m) e),
        pfdFace (fkSquareBoxPlanar m)
          (kwg_flankRight (fkSquareBoxPlanar m) e)) =
      s(pfdFace (fkSquareBoxPlanar m) x.1, z) at hends
    rw [Sym2.eq_iff] at hends
    rcases hends with hends | hends
    · have hL : kwg_flankLeft (fkSquareBoxPlanar m) e = x.1 :=
        (pfdFace_eq_inner_iff hNm x.2).mp hends.1
      have hxy : (hypercubicLattice 2).Adj x.1
          (kwg_flankRight (fkSquareBoxPlanar m) e) := by
        simpa [hL] using kwg_flanks_adj (fkSquareBoxPlanar m) e
      have hy : kwg_flankRight (fkSquareBoxPlanar m) e ∈ box 2 N := by
        have := ccb_adj_mem_box_succ hxy hxinner
        simpa [Nat.sub_add_cancel hN] using this
      let y : FK.boxVerts 2 N :=
        ⟨kwg_flankRight (fkSquareBoxPlanar m) e, hy⟩
      have hz : fkSquareBox_innerFaceMap N m y = z := by
        simpa [fkSquareBox_innerFaceMap, y] using hends.2
      apply hrange
      refine ⟨s(x, y), ?_⟩
      rw [ocd_innerEdge_mk, hz]
    · have hR : kwg_flankRight (fkSquareBoxPlanar m) e = x.1 :=
        (pfdFace_eq_inner_iff hNm x.2).mp hends.2
      have hxy : (hypercubicLattice 2).Adj x.1
          (kwg_flankLeft (fkSquareBoxPlanar m) e) := by
        simpa [hR] using (kwg_flanks_adj (fkSquareBoxPlanar m) e).symm
      have hy : kwg_flankLeft (fkSquareBoxPlanar m) e ∈ box 2 N := by
        have := ccb_adj_mem_box_succ hxy hxinner
        simpa [Nat.sub_add_cancel hN] using this
      let y : FK.boxVerts 2 N :=
        ⟨kwg_flankLeft (fkSquareBoxPlanar m) e, hy⟩
      have hz : fkSquareBox_innerFaceMap N m y = z := by
        simpa [fkSquareBox_innerFaceMap, y] using hends.1
      apply hrange
      refine ⟨s(x, y), ?_⟩
      rw [ocd_innerEdge_mk, hz]
  · exact hxfalse.elim



theorem fkSquareBox_inducedWiring_le_boundaryClique
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    (psi : ConfigSpace (Sym2 (kwg_Face (fkSquareBoxPlanar m)))) :
    ocd_inducedWiring (fkSquareBoxFullDualGraph m)
        (fkSquareBox_innerFaceMap N m) (fun _ => False) psi ≤
      boundaryCliqueGraph (FK.boxBoundary 2 N) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : fkSquareBox_innerFaceMap N m x ≠
        fkSquareBox_innerFaceMap N m y :=
      fun heq => hne (fkSquareBox_innerFaceMap_injective hNm heq)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact fkSquareBox_boundary_of_outsideGraph_adj hNm hN psi hadj
  · have hreach' :
        (ocd_outsideGraph (fkSquareBoxFullDualGraph m)
          (fkSquareBox_innerFaceMap N m) (fun _ => False) psi).Reachable
            (fkSquareBox_innerFaceMap N m y)
            (fkSquareBox_innerFaceMap N m x) := hreach.symm
    have hne' : fkSquareBox_innerFaceMap N m y ≠
        fkSquareBox_innerFaceMap N m x :=
      fun heq => hne (fkSquareBox_innerFaceMap_injective hNm heq).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact fkSquareBox_boundary_of_outsideGraph_adj hNm hN psi hadj

end

end StatMech.FrontierD

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CellEulerFaithful
import Code.Onsager.EdgeUnique










namespace StatMech.Onsager.GeneralInterior

open Finset SimpleGraph Set
open StatMech.Lattice
open StatMech.Euc
open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH
  StatMech.Onsager.EdgeUnique StatMech.Onsager.InteriorCells
  StatMech.Onsager.WalkCellRegion StatMech.Onsager.CellCount
  StatMech.Onsager.CellEuler StatMech.Onsager.CellEulerFaithful

variable {n : ℕ} [NeZero n]


theorem exists_odd_cell_at_edge (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (k : Fin n) :
    ∃ c : ℤ × ℤ, rayParity d c.1 c.2 = 1 := by
  set p := pos d k
  have hs := pos_succ d hclosed k
  match hd : d k with
  | 0 =>
      have hpk : pos d (k + 1) = (p.1 + 1, p.2) := by
        rw [hs, hd]
        ext <;> simp [p, stepOf]
      have hmem : k ∈ midSet d p.1 p.2 := by
        simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Or.inl hd, ?_, ?_⟩
        · rw [hpk]
          simp [p]
        · simp [p]
      have hflip : rayParity d p.1 (p.2 - 1) = rayParity d p.1 p.2 + 1 := by
        have h := rayParity_vflip d p.1 (p.2 - 1)
          (by
            rw [show p.2 - 1 + 1 = p.2 by ring]
            exact midSet_card_odd_of_mem d hclosed hsimple hn p.1 p.2 k hmem)
        rwa [show p.2 - 1 + 1 = p.2 by ring] at h
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d p.1 p.2) with h0 | h1
      · refine ⟨(p.1, p.2 - 1), ?_⟩
        simpa [h0] using hflip
      · exact ⟨(p.1, p.2), h1⟩
  | 1 =>
      have hpk : pos d (k + 1) = (p.1, p.2 + 1) := by
        rw [hs, hd]
        ext <;> simp [p, stepOf]
      have hmem : k ∈ straddleSet d (p.1 - 1) p.2 := by
        simp only [straddleSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Or.inl hd, ?_, ?_, ?_⟩
        · simp [p]
        · rw [hpk]
          simp [p]
        · rw [hpk]
          simp [p]
      have hflip : rayParity d (p.1 - 1) p.2 = rayParity d p.1 p.2 + 1 := by
        have h := rayParity_hflip d hclosed (p.1 - 1) p.2
          (straddleSet_card_odd_of_mem d hclosed hsimple hn (p.1 - 1) p.2 k hmem)
        rwa [show p.1 - 1 + 1 = p.1 by ring] at h
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d p.1 p.2) with h0 | h1
      · refine ⟨(p.1 - 1, p.2), ?_⟩
        simpa [h0] using hflip
      · exact ⟨(p.1, p.2), h1⟩
  | 2 =>
      have hpk : pos d (k + 1) = (p.1 - 1, p.2) := by
        rw [hs, hd]
        ext <;> simp [p, stepOf] <;> ring
      have hmem : k ∈ midSet d (p.1 - 1) p.2 := by
        simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Or.inr hd, ?_, ?_⟩
        · rw [hpk]
          simp [p]
        · simp [p]
      have hflip : rayParity d (p.1 - 1) (p.2 - 1) = rayParity d (p.1 - 1) p.2 + 1 := by
        have h := rayParity_vflip d (p.1 - 1) (p.2 - 1)
          (by
            rw [show p.2 - 1 + 1 = p.2 by ring]
            exact midSet_card_odd_of_mem d hclosed hsimple hn (p.1 - 1) p.2 k hmem)
        rwa [show p.2 - 1 + 1 = p.2 by ring] at h
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
          (rayParity d (p.1 - 1) p.2) with h0 | h1
      · refine ⟨(p.1 - 1, p.2 - 1), ?_⟩
        simpa [h0] using hflip
      · exact ⟨(p.1 - 1, p.2), h1⟩
  | 3 =>
      have hpk : pos d (k + 1) = (p.1, p.2 - 1) := by
        rw [hs, hd]
        ext <;> simp [p, stepOf] <;> ring
      have hmem : k ∈ straddleSet d (p.1 - 1) (p.2 - 1) := by
        simp only [straddleSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Or.inr hd, ?_, ?_, ?_⟩
        · simp [p]
        · rw [hpk]
          simp [p]
        · rw [hpk]
          simp [p]
      have hflip : rayParity d (p.1 - 1) (p.2 - 1) = rayParity d p.1 (p.2 - 1) + 1 := by
        have h := rayParity_hflip d hclosed (p.1 - 1) (p.2 - 1)
          (straddleSet_card_odd_of_mem d hclosed hsimple hn (p.1 - 1) (p.2 - 1) k hmem)
        rwa [show p.1 - 1 + 1 = p.1 by ring] at h
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
          (rayParity d p.1 (p.2 - 1)) with h0 | h1
      · refine ⟨(p.1 - 1, p.2 - 1), ?_⟩
        simpa [h0] using hflip
      · exact ⟨(p.1, p.2 - 1), h1⟩


theorem interiorCells_nonempty (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) : (interiorCells d hclosed).Nonempty := by
  obtain ⟨c, hc⟩ := exists_odd_cell_at_edge d hclosed hsimple hn 0
  exact ⟨c, (mem_interiorCells d hclosed c).2 hc⟩

section WalkRegion

variable {m : ℕ}


noncomputable def oddComponent (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (c : interiorCells d hclosed) :
    (walkRegionGraph d hclosed hsimple).ConnectedComponent :=
  (walkRegionGraph d hclosed hsimple).connectedComponentMk (cellFace c.1)


theorem oddComponent_finite (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (c : interiorCells d hclosed) :
    (oddComponent d hclosed hsimple c).supp.Finite := by
  apply (jfc_whb_bounded_iff_ne_outer (walkP d hclosed hsimple)
    (oddComponent d hclosed hsimple c)).2
  intro heq
  have hreach : (walkRegionGraph d hclosed hsimple).Reachable (cellFace c.1)
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) :=
    ConnectedComponent.eq.mp heq
  have hpar := rayParity_eq_of_reachable d hclosed hsimple hreach
  have hc : rayParity d c.1.1 c.1.2 = 1 :=
    (mem_interiorCells d hclosed c.1).mp c.2
  simpa [hc, outerBeacon_parity d hclosed hsimple] using hpar


theorem odd_cells_reachable (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (c e : interiorCells d hclosed) :
    (walkRegionGraph d hclosed hsimple).Reachable (cellFace c.1) (cellFace e.1) := by
  let C : jcb_BoundedRegion (walkP d hclosed hsimple) :=
    ⟨oddComponent d hclosed hsimple c, oddComponent_finite d hclosed hsimple c⟩
  let E : jcb_BoundedRegion (walkP d hclosed hsimple) :=
    ⟨oddComponent d hclosed hsimple e, oddComponent_finite d hclosed hsimple e⟩
  letI : Unique (jcb_BoundedRegion (walkP d hclosed hsimple)) :=
    jcb_uniqueBoundedRegion_of_nullity_one (walkP d hclosed hsimple)
      (StatMech.Onsager.JedBridge.walkSubgraph_nullity_one d hclosed hsimple)
  have hCE : C = E := Subsingleton.elim _ _
  exact ConnectedComponent.eq.mp (congrArg Subtype.val hCE)



theorem even_cell_reaches_beacon (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (p : ℤ × ℤ) (hp : rayParity d p.1 p.2 = 0) :
    (walkRegionGraph d hclosed hsimple).Reachable (cellFace p)
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := by
  let C := (walkRegionGraph d hclosed hsimple).connectedComponentMk (cellFace p)
  have hC : C = jfc_whb_outerRegion (walkP d hclosed hsimple) := by
    by_contra hne
    have hCfin : C.supp.Finite :=
      (jfc_whb_bounded_iff_ne_outer (walkP d hclosed hsimple) C).2 hne
    obtain ⟨c, hc⟩ := interiorCells_nonempty d hclosed hsimple (by omega)
    let boundedC : jcb_BoundedRegion (walkP d hclosed hsimple) := ⟨C, hCfin⟩
    let boundedOdd : jcb_BoundedRegion (walkP d hclosed hsimple) :=
      ⟨oddComponent d hclosed hsimple ⟨c, hc⟩,
        oddComponent_finite d hclosed hsimple ⟨c, hc⟩⟩
    letI : Unique (jcb_BoundedRegion (walkP d hclosed hsimple)) :=
      jcb_uniqueBoundedRegion_of_nullity_one (walkP d hclosed hsimple)
        (StatMech.Onsager.JedBridge.walkSubgraph_nullity_one d hclosed hsimple)
    have heq : boundedC = boundedOdd := Subsingleton.elim _ _
    have hreach : (walkRegionGraph d hclosed hsimple).Reachable (cellFace p) (cellFace c) :=
      ConnectedComponent.eq.mp (congrArg Subtype.val heq)
    have hpar := rayParity_eq_of_reachable d hclosed hsimple hreach
    have hcpar : rayParity d c.1 c.2 = 1 := (mem_interiorCells d hclosed c).mp hc
    have hpar' : rayParity d p.1 p.2 = rayParity d c.1 c.2 := by simpa using hpar
    rw [hp, hcpar] at hpar'
    exact zero_ne_one hpar'
  exact ConnectedComponent.eq.mp hC


theorem outside_cell_reaches_beacon (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (p : ℤ × ℤ) (hp : p ∉ InteriorCells.interiorCells d hclosed) :
    (walkRegionGraph d hclosed hsimple).Reachable (cellFace p)
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := by
  apply even_cell_reaches_beacon d hclosed hsimple p
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d p.1 p.2) with h0 | h1
  · exact h0
  · exact absurd ((mem_interiorCells d hclosed p).2 h1) hp



theorem vertical_sharedEdge_mem_regEdges_iff (S : Finset (ℤ × ℤ)) (x y : ℤ) :
    Sym2.map cellFace.symm
        (sharedPrimalEdge (cellFace (x, y)) (cellFace (x + 1, y))) ∈ StatMech.Euc.regEdges S ↔
      (x, y) ∈ S ∨ (x + 1, y) ∈ S := by
  change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x + 1, y]) ∈
      StatMech.Euc.regEdges S ↔ _
  rw [sharedPrimalEdge_right]
  simp only [faceCorner10, faceCorner11, Sym2.map_mk, cellFace_symm]
  constructor
  · intro h
    rw [StatMech.Euc.regEdges, Finset.mem_biUnion] at h
    obtain ⟨c, hc, he⟩ := h
    obtain ⟨u, v⟩ := c
    simp only [StatMech.Euc.cellEdges, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff, Prod.mk.injEq] at he
    rcases he with he | he | he | he <;>
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all <;> omega
  · rintro (hp | hq)
    · rw [StatMech.Euc.regEdges, Finset.mem_biUnion]
      refine ⟨(x, y), hp, ?_⟩
      simp [StatMech.Euc.cellEdges]
    · rw [StatMech.Euc.regEdges, Finset.mem_biUnion]
      refine ⟨(x + 1, y), hq, ?_⟩
      simp [StatMech.Euc.cellEdges]



theorem horizontal_sharedEdge_mem_regEdges_iff (S : Finset (ℤ × ℤ)) (x y : ℤ) :
    Sym2.map cellFace.symm
        (sharedPrimalEdge (cellFace (x, y)) (cellFace (x, y + 1))) ∈ StatMech.Euc.regEdges S ↔
      (x, y) ∈ S ∨ (x, y + 1) ∈ S := by
  change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x, y + 1]) ∈
      StatMech.Euc.regEdges S ↔ _
  rw [sharedPrimalEdge_top]
  simp only [faceCorner01, faceCorner11, Sym2.map_mk, cellFace_symm]
  constructor
  · intro h
    rw [StatMech.Euc.regEdges, Finset.mem_biUnion] at h
    obtain ⟨c, hc, he⟩ := h
    obtain ⟨u, v⟩ := c
    simp only [StatMech.Euc.cellEdges, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff, Prod.mk.injEq] at he
    rcases he with he | he | he | he <;>
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all <;> omega
  · rintro (hp | hq)
    · rw [StatMech.Euc.regEdges, Finset.mem_biUnion]
      refine ⟨(x, y), hp, ?_⟩
      simp [StatMech.Euc.cellEdges]
    · rw [StatMech.Euc.regEdges, Finset.mem_biUnion]
      refine ⟨(x, y + 1), hq, ?_⟩
      simp [StatMech.Euc.cellEdges]



theorem sharedEdge_mem_regEdges_iff (S : Finset (ℤ × ℤ)) (p q : ℤ × ℤ)
    (hlat : (hypercubicLattice 2).Adj (cellFace p) (cellFace q)) :
    Sym2.map cellFace.symm (sharedPrimalEdge (cellFace p) (cellFace q)) ∈
        StatMech.Euc.regEdges S ↔ p ∈ S ∨ q ∈ S := by
  obtain ⟨x, y⟩ := p
  have hdist := hlat
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hdist
  simp only [cellFace_zero, cellFace_one] at hdist
  have hcases : q = (x + 1, y) ∨ q = (x - 1, y) ∨
      q = (x, y + 1) ∨ q = (x, y - 1) := by
    by_cases hx : q.1 = x
    · have hy : q.2 = y + 1 ∨ q.2 = y - 1 := by
        have : (y - q.2).natAbs = 1 := by omega
        rcases Int.natAbs_eq_iff.mp this with h | h <;> omega
      rcases hy with hy | hy
      · right; right; left; exact Prod.ext hx hy
      · right; right; right; exact Prod.ext hx hy
    · have hy : q.2 = y := by omega
      have hx' : q.1 = x + 1 ∨ q.1 = x - 1 := by
        have : (x - q.1).natAbs = 1 := by omega
        rcases Int.natAbs_eq_iff.mp this with h | h <;> omega
      rcases hx' with hx' | hx'
      · left; exact Prod.ext hx' hy
      · right; left; exact Prod.ext hx' hy
  rcases hcases with rfl | rfl | rfl | rfl
  · exact vertical_sharedEdge_mem_regEdges_iff S x y
  · have h := vertical_sharedEdge_mem_regEdges_iff S (x - 1) y
    have hcomm := sharedPrimalEdge_comm_of_adj hlat
    rw [hcomm]
    simpa [or_comm] using h
  · exact horizontal_sharedEdge_mem_regEdges_iff S x y
  · have h := horizontal_sharedEdge_mem_regEdges_iff S x (y - 1)
    have hcomm := sharedPrimalEdge_comm_of_adj hlat
    rw [hcomm]
    simpa [or_comm] using h



theorem regEdge_of_mem_cellSkeleton_image (S : Finset (ℤ × ℤ))
    (e : Sym2 (Site 2))
    (he : e ∈ (imageGraph (cellSkeletonP S)).edgeSet) :
    Sym2.map cellFace.symm e ∈ StatMech.Euc.regEdges S := by
  induction e with
  | h f g =>
      rw [SimpleGraph.mem_edgeSet, imageGraph_adj] at he
      obtain ⟨a, b, hab, ha, hb⟩ := he
      change s(a.1, b.1) ∈ StatMech.Euc.regEdges S at hab
      simp only [Sym2.map_mk]
      have ha' : cellFace a.1 = f := by simpa [cellSkeletonP] using ha
      have hb' : cellFace b.1 = g := by simpa [cellSkeletonP] using hb
      rw [← ha', ← hb']
      simpa using hab



theorem outside_faceAdj_cellSkeleton (S : Finset (ℤ × ℤ)) (p q : ℤ × ℤ)
    (hp : p ∉ S) (hq : q ∉ S)
    (hlat : (hypercubicLattice 2).Adj (cellFace p) (cellFace q)) :
    (whb_faceRegion (imageGraph (cellSkeletonP S))).Adj (cellFace p) (cellFace q) := by
  rw [whb_faceRegion_adj]
  refine ⟨hlat, ?_⟩
  intro hedge
  have hreg := regEdge_of_mem_cellSkeleton_image S _ hedge
  rcases (sharedEdge_mem_regEdges_iff S p q hlat).mp hreg with h | h
  · exact hp h
  · exact hq h



theorem outside_cell_reaches_beacon_cellSkeleton (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (p : ℤ × ℤ) (hp : p ∉ InteriorCells.interiorCells d hclosed) :
    (whb_faceRegion (imageGraph
      (cellSkeletonP (InteriorCells.interiorCells d hclosed)))).Reachable (cellFace p)
        (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := by
  let S := InteriorCells.interiorCells d hclosed
  obtain ⟨w⟩ := outside_cell_reaches_beacon d hclosed hsimple p hp
  have lift : ∀ {f g : Site 2} (q : (walkRegionGraph d hclosed hsimple).Walk f g)
      (hf : cellFace.symm f ∉ S) (hg : cellFace.symm g ∉ S),
      (whb_faceRegion (imageGraph (cellSkeletonP S))).Reachable f g := by
    intro f g q
    induction q with
    | nil => intro _ _; exact Reachable.refl _
    | @cons a b z hab q ih =>
        intro ha hz
        have hb : cellFace.symm b ∉ S := by
          intro hbS
          have hbpar : rayParity d (cellFace.symm b).1 (cellFace.symm b).2 = 1 :=
            (mem_interiorCells d hclosed (cellFace.symm b)).mp hbS
          have hpar := rayParity_eq_of_faceAdj d hclosed hsimple hab
          have hap : rayParity d (cellFace.symm a).1 (cellFace.symm a).2 = 1 := by
            have hpar' : rayParity d (cellFace.symm a).1 (cellFace.symm a).2 =
                rayParity d (cellFace.symm b).1 (cellFace.symm b).2 := by
              simpa [cellFace_symm] using hpar
            exact hpar'.trans hbpar
          exact ha ((mem_interiorCells d hclosed (cellFace.symm a)).2 hap)
        have hstep : (whb_faceRegion (imageGraph (cellSkeletonP S))).Adj a b := by
          simpa using outside_faceAdj_cellSkeleton S (cellFace.symm a) (cellFace.symm b)
            ha hb (by simpa using hab.1)
        exact hstep.reachable.trans (ih hb hz)
  apply lift w
  · simpa [S] using hp
  · have hout : rayParity d
        (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 0)
        (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 1) = 0 :=
      outerBeacon_parity d hclosed hsimple
    intro hmem
    have hone := (mem_interiorCells d hclosed
      (cellFace.symm (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)))).mp hmem
    have hone' : rayParity d
        (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 0)
        (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 1) = 1 := by
      simpa [cellFace_symm] using hone
    rw [hout] at hone'
    exact zero_ne_one hone'



theorem outside_cell_component_eq_outer (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (p : ℤ × ℤ) (hp : p ∉ InteriorCells.interiorCells d hclosed) :
    (whb_faceRegion (imageGraph
      (cellSkeletonP (InteriorCells.interiorCells d hclosed)))).connectedComponentMk (cellFace p) =
        jfc_whb_outerRegion (cellSkeletonP (InteriorCells.interiorCells d hclosed)) := by
  let S := InteriorCells.interiorCells d hclosed
  let P := cellSkeletonP S
  let Rw := outerBoxRadius (walkP d hclosed hsimple)
  let towerCell : ℕ → ℤ × ℤ := fun t => ((Rw : ℤ) + 2, (Rw : ℤ) + 2 + t)
  have htowerOut : ∀ t, towerCell t ∉ S := by
    intro t ht
    have htpar := (mem_interiorCells d hclosed (towerCell t)).mp ht
    have hzero : rayParity d (towerCell t).1 (towerCell t).2 = 0 := by
      apply rayParity_topOutside d _ _ (Rw : ℤ)
      · intro j
        have hj := outerBoxRadius_spec (walkP d hclosed hsimple) j
        rw [mem_box] at hj
        have hj1 := hj 1
        change (pos d j).2.natAbs ≤ Rw at hj1
        omega
      · push_cast
        simp [towerCell]
        omega
    rw [hzero] at htpar
    exact zero_ne_one htpar
  have htowerStep : ∀ t,
      (whb_faceRegion (imageGraph P)).Adj (cellFace (towerCell t)) (cellFace (towerCell (t + 1))) := by
    intro t
    apply outside_faceAdj_cellSkeleton S (towerCell t) (towerCell (t + 1))
      (htowerOut t) (htowerOut (t + 1))
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    simp [towerCell]
  have htowerReach : ∀ t,
      (whb_faceRegion (imageGraph P)).Reachable (cellFace (towerCell 0)) (cellFace (towerCell t)) := by
    intro t
    induction t with
    | zero => exact Reachable.refl _
    | succ t ih => exact ih.trans (htowerStep t).reachable
  have hbase := outside_cell_reaches_beacon_cellSkeleton d hclosed hsimple p hp
  have hbase' : (whb_faceRegion (imageGraph P)).Reachable
      (cellFace p) (cellFace (towerCell 0)) := by
    have hbeq : cellFace (towerCell 0) = beacon 2 (Rw + 1) := by
      funext i
      fin_cases i <;> simp [towerCell, beacon] <;> push_cast <;> ring
    rw [hbeq]
    exact hbase
  let t := outerBoxRadius P + 2
  have htarget : cellFace (towerCell t) ∈ exterior 2 (outerBoxRadius P + 1) := by
    refine ⟨1, ?_⟩
    simp [towerCell, t]
    omega
  have houter := jfc_whb_exterior_in_outerRegion P htarget
  have hreach := hbase'.trans (htowerReach t)
  exact (ConnectedComponent.eq.mpr hreach).trans houter



theorem occupiedBoundedFace_surjective (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    Function.Surjective
      (occupiedBoundedFace (InteriorCells.interiorCells d hclosed)) := by
  let S := InteriorCells.interiorCells d hclosed
  let P := cellSkeletonP S
  intro B
  obtain ⟨g, hg⟩ := Quot.exists_rep B.1
  have hrep : (whb_faceRegion (imageGraph P)).connectedComponentMk g = B.1 := by
    simpa [P] using hg
  let p := cellFace.symm g
  by_cases hp : p ∈ S
  · refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    change occupiedComponent S p = B.1
    unfold occupiedComponent
    have hpg : cellFace p = g := cellFace.apply_symm_apply g
    rw [hpg]
    exact hrep
  · exfalso
    have hout : (whb_faceRegion (imageGraph P)).connectedComponentMk (cellFace p) =
        jfc_whb_outerRegion P := by
      simpa [P, S] using outside_cell_component_eq_outer d hclosed hsimple p hp
    have hpg : cellFace p = g := cellFace.apply_symm_apply g
    rw [hpg] at hout
    have hBout : B.1 = jfc_whb_outerRegion P := hrep.symm.trans hout
    exact (jfc_whb_outerRegion_infinite P) (hBout ▸ B.2)



theorem cellSkeleton_nullity_eq_card (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    nullity (cellSkeleton (InteriorCells.interiorCells d hclosed)) =
      (InteriorCells.interiorCells d hclosed).card := by
  let S := InteriorCells.interiorCells d hclosed
  let e : S ≃ jcb_BoundedRegion (cellSkeletonP S) :=
    Equiv.ofBijective (occupiedBoundedFace S)
      ⟨occupiedBoundedFace_injective S, occupiedBoundedFace_surjective d hclosed hsimple⟩
  calc
    nullity (cellSkeleton S) = Nat.card (jcb_BoundedRegion (cellSkeletonP S)) := by
      exact (jcb_boundedRegion_card_eq_nullity (cellSkeletonP S)).symm
    _ = Nat.card S := (Nat.card_congr e).symm
    _ = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]



theorem interior_cellSkeleton_connected (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    (cellSkeleton (InteriorCells.interiorCells d hclosed)).Connected := by
  let S : Finset (ℤ × ℤ) := InteriorCells.interiorCells d hclosed
  rw [connected_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    rw [regVerts, Finset.mem_biUnion] at hu hv
    obtain ⟨c, hc, huc⟩ := hu
    obtain ⟨e, he, hve⟩ := hv
    have hucRep : (cellSkeleton S).Reachable ⟨u, hu⟩
        (skeletonRepresentative S ⟨c, hc⟩) := by
      simpa [S, skeletonRepresentative, skeletonVertexOfCorner] using
        corner_reachable_lowerLeft S c hc u huc
    have hce : (walkRegionGraph d hclosed hsimple).Reachable (cellFace c) (cellFace e) :=
      odd_cells_reachable d hclosed hsimple ⟨c, hc⟩ ⟨e, he⟩
    obtain ⟨p⟩ := hce
    have cellMem : ∀ (f : Site 2), f ∈ (oddComponent d hclosed hsimple ⟨c, hc⟩).supp →
        cellFace.symm f ∈ S := by
      intro f hf
      have hreach : (walkRegionGraph d hclosed hsimple).Reachable f (cellFace c) := by
        have hcomp :=
          (oddComponent d hclosed hsimple ⟨c, hc⟩).mem_supp_iff f |>.mp hf
        exact ConnectedComponent.eq.mp hcomp
      have hpar := rayParity_eq_of_reachable d hclosed hsimple hreach
      have hcpar : rayParity d c.1 c.2 = 1 := (mem_interiorCells d hclosed c).mp hc
      apply (mem_interiorCells d hclosed (cellFace.symm f)).2
      simpa [cellFace_symm, hcpar] using hpar
    have lift : ∀ {f g : Site 2} (q : (walkRegionGraph d hclosed hsimple).Walk f g)
        (hf : f ∈ (oddComponent d hclosed hsimple ⟨c, hc⟩).supp)
        (hg : g ∈ (oddComponent d hclosed hsimple ⟨c, hc⟩).supp),
        (cellSkeleton S).Reachable
          (skeletonRepresentative S ⟨cellFace.symm f, cellMem f hf⟩)
          (skeletonRepresentative S ⟨cellFace.symm g, cellMem g hg⟩) := by
      intro f g q
      induction q with
      | nil => intro _ _; exact Reachable.refl _
      | @cons a b z hab q ih =>
          intro ha hz
          have hb := (oddComponent d hclosed hsimple ⟨c, hc⟩).mem_supp_of_adj_mem_supp ha hab
          have hlat : (hypercubicLattice 2).Adj
              (cellFace (cellFace.symm a)) (cellFace (cellFace.symm b)) := by
            simpa using hab.1
          have hstep := cell_representatives_reachable_of_adj S
            (cellFace.symm a) (cellFace.symm b) (cellMem a ha) (cellMem b hb) hlat
          have hstep' : (cellSkeleton S).Reachable
              (skeletonRepresentative S ⟨cellFace.symm a, cellMem a ha⟩)
              (skeletonRepresentative S ⟨cellFace.symm b, cellMem b hb⟩) := by
            simpa [skeletonRepresentative] using hstep
          exact hstep'.trans (ih hb hz)
    have hcSupp : cellFace c ∈ (oddComponent d hclosed hsimple ⟨c, hc⟩).supp := by
      rw [ConnectedComponent.mem_supp_iff]
      rfl
    have heSupp : cellFace e ∈ (oddComponent d hclosed hsimple ⟨c, hc⟩).supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact ConnectedComponent.eq.mpr p.reverse.reachable
    have hceSkel := lift p hcSupp heSupp
    have hevRep : (cellSkeleton S).Reachable ⟨v, hv⟩
        (skeletonRepresentative S ⟨e, he⟩) := by
      simpa [S, skeletonRepresentative, skeletonVertexOfCorner] using
        corner_reachable_lowerLeft S e he v hve
    exact hucRep.trans (by simpa [S, skeletonRepresentative] using hceSkel) |>.trans hevRep.symm
  · obtain ⟨c, hc⟩ := interiorCells_nonempty d hclosed hsimple (by omega)
    exact ⟨skeletonRepresentative S ⟨c, by simpa [S] using hc⟩⟩


theorem eulerChar_interiorCells_le_one (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    eulerChar (InteriorCells.interiorCells d hclosed) ≤ 1 :=
  eulerChar_le_one_of_skeleton_connected _
    (interior_cellSkeleton_connected d hclosed hsimple)



theorem eulerChar_interiorCells_eq_one (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    eulerChar (InteriorCells.interiorCells d hclosed) = 1 := by
  let S := InteriorCells.interiorCells d hclosed
  change eulerChar S = 1
  have hconn : (cellSkeleton S).Connected := by
    simpa [S] using interior_cellSkeleton_connected d hclosed hsimple
  have hnull : nullity (cellSkeleton S) = S.card := by
    simpa [S] using cellSkeleton_nullity_eq_card d hclosed hsimple
  have hcomp : Nat.card (cellSkeleton S).ConnectedComponent = 1 :=
    card_components_eq_one_of_connected hconn
  have hvertices := card_cellSkeleton_vertices S
  have hedges := card_cellSkeleton_edges S
  have hedges' : (cellSkeleton S).edgeSet.ncard =
      (StatMech.Euc.regEdges S).card := by
    rw [← Nat.card_coe_set_eq, hedges]
  have htree := hconn.card_vert_le_card_edgeSet_add_one
  rw [hvertices, hedges] at htree
  unfold nullity at hnull
  rw [hcomp, hvertices, hedges'] at hnull
  rw [StatMech.Onsager.CellEulerBound.eulerChar_eq_regChi]
  unfold regChi
  push_cast
  omega

end WalkRegion

end StatMech.Onsager.GeneralInterior

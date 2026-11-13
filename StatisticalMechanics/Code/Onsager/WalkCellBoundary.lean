/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.WalkCellLocal
import Code.Onsager.WalkCellBridge

namespace StatMech.Onsager.WalkCellBoundary

open Finset SimpleGraph Set
open StatMech.Lattice
open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.JedBridge StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellLocal StatMech.Onsager.CellCount
  StatMech.Onsager.CellEuler StatMech.Onsager.CellPinch
  StatMech.Onsager.CellConnect StatMech.Onsager.WalkCellBridge

variable {m : ℕ}


def leftCell (d : Fin (m + 3) → Fin 4) (k : Fin (m + 3)) : ℤ × ℤ :=
  match d k with
  | 0 => ((pos d k).1, (pos d k).2)
  | 1 => ((pos d k).1 - 1, (pos d k).2)
  | 2 => ((pos d k).1 - 1, (pos d k).2 - 1)
  | 3 => ((pos d k).1, (pos d k).2 - 1)


def rightCell (d : Fin (m + 3) → Fin 4) (k : Fin (m + 3)) : ℤ × ℤ :=
  match d k with
  | 0 => ((pos d k).1, (pos d k).2 - 1)
  | 1 => ((pos d k).1, (pos d k).2)
  | 2 => ((pos d k).1 - 1, (pos d k).2)
  | 3 => ((pos d k).1 - 1, (pos d k).2 - 1)

theorem imageGraph_not_adj_of_neighbours (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (k : Fin (m + 3)) (q : Site 2)
    (hpred : q ≠ posSite d (k - 1)) (hsucc : q ≠ posSite d (k + 1)) :
    ¬ (imageGraph (walkP d hclosed hsimple)).Adj (posSite d k) q := by
  rw [imageGraph_adj_pos_iff d hclosed hsimple k q]
  tauto



theorem leftCell_faceAdj_of_straight (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (k : Fin (m + 3)) (hstraight : d (k + 1) = d k) :
    (walkRegionGraph d hclosed hsimple).Adj (cellFace (leftCell d k))
      (cellFace (leftCell d (k + 1))) := by
  have hpos := pos_succ d hclosed k
  have hpos' := pos_succ d hclosed (k + 1)
  generalize hp : pos d k = p at hpos
  obtain ⟨x, y⟩ := p
  generalize hd : d k = a
  fin_cases a
  · have hdn : d (k + 1) = 0 := hstraight.trans hd
    have hn : pos d (k + 1) = (x + 1, y) := by simpa [hp, hd, stepOf] using hpos
    have hnn : pos d (k + 1 + 1) = (x + 2, y) := by
      rw [hn, hdn] at hpos'
      simp only [stepOf] at hpos'
      calc
        pos d (k + 1 + 1) = (x + 1, y) + (1, 0) := hpos'
        _ = (x + 2, y) := by ext <;> simp <;> omega
    constructor
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [leftCell, hd, hdn, hp, hn]
    · intro hedge
      simp [leftCell, hd, hdn, hp, hn] at hedge
      have he : s((![x + 1, y] : Site 2), ![x + 1, y + 1]) ∈
          (imageGraph (walkP d hclosed hsimple)).edgeSet := by
        change sharedPrimalEdge ![x, y] ![x + 1, y] ∈ _ at hedge
        rw [sharedPrimalEdge_right] at hedge
        simpa [faceCorner10, faceCorner11] using hedge
      have ha : (imageGraph (walkP d hclosed hsimple)).Adj
          ![x + 1, y] ![x + 1, y + 1] := by rwa [← SimpleGraph.mem_edgeSet]
      rcases (imageGraph_adj_pos_iff d hclosed hsimple (k + 1)
        ![x + 1, y + 1]).mp (by simpa [posSite, hn] using ha) with h | h
      · have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [posSite, hp] at h0 h1
      · have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [posSite, hnn] at h0 h1
  · have hdn : d (k + 1) = 1 := hstraight.trans hd
    have hn : pos d (k + 1) = (x, y + 1) := by simpa [hp, hd, stepOf] using hpos
    have hnn : pos d (k + 1 + 1) = (x, y + 2) := by
      rw [hn, hdn] at hpos'
      simp only [stepOf] at hpos'
      calc
        pos d (k + 1 + 1) = (x, y + 1) + (0, 1) := hpos'
        _ = (x, y + 2) := by ext <;> simp <;> omega
    constructor
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [leftCell, hd, hdn, hp, hn]
    · intro hedge
      simp [leftCell, hd, hdn, hp, hn] at hedge
      have he : s((![x - 1, y + 1] : Site 2), ![x, y + 1]) ∈
          (imageGraph (walkP d hclosed hsimple)).edgeSet := by
        change sharedPrimalEdge ![x - 1, y] ![x - 1, y + 1] ∈ _ at hedge
        rw [sharedPrimalEdge_top] at hedge
        simpa [faceCorner01, faceCorner11] using hedge
      have ha : (imageGraph (walkP d hclosed hsimple)).Adj
          ![x, y + 1] ![x - 1, y + 1] := by
        rw [← SimpleGraph.mem_edgeSet, Sym2.eq_swap]
        exact he
      rcases (imageGraph_adj_pos_iff d hclosed hsimple (k + 1)
        ![x - 1, y + 1]).mp (by simpa [posSite, hn] using ha) with h | h
      · have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [posSite, hp] at h0 h1
      · have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [posSite, hnn] at h0 h1
  · have hdn : d (k + 1) = 2 := hstraight.trans hd
    have hn : pos d (k + 1) = (x - 1, y) := by simpa [hp, hd, stepOf] using hpos
    have hnn : pos d (k + 1 + 1) = (x - 2, y) := by
      rw [hn, hdn] at hpos'
      simp only [stepOf] at hpos'
      calc
        pos d (k + 1 + 1) = (x - 1, y) + (-1, 0) := hpos'
        _ = (x - 2, y) := by ext <;> simp <;> omega
    constructor
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [leftCell, hd, hdn, hp, hn]
    · intro hedge
      simp [leftCell, hd, hdn, hp, hn] at hedge
      ring_nf at hedge
      have he : s((![x - 1, y - 1] : Site 2), ![x - 1, y]) ∈
          (imageGraph (walkP d hclosed hsimple)).edgeSet := by
        change sharedPrimalEdge ![-1 + x, -1 + y] ![-2 + x, -1 + y] ∈ _ at hedge
        rw [show -2 + x = (-1 + x) - 1 by ring] at hedge
        rw [sharedPrimalEdge_left] at hedge
        simp only [faceCorner00, faceCorner01] at hedge
        ring_nf at hedge
        simpa only [sub_eq_add_neg, add_comm] using hedge
      have ha : (imageGraph (walkP d hclosed hsimple)).Adj
          ![x - 1, y] ![x - 1, y - 1] := by
        rw [← SimpleGraph.mem_edgeSet, Sym2.eq_swap]
        exact he
      rcases (imageGraph_adj_pos_iff d hclosed hsimple (k + 1)
        ![x - 1, y - 1]).mp (by simpa [posSite, hn] using ha) with h | h
      · have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [posSite, hp] at h0 h1
      · have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [posSite, hnn] at h0 h1
  · have hdn : d (k + 1) = 3 := hstraight.trans hd
    have hn : pos d (k + 1) = (x, y - 1) := by simpa [hp, hd, stepOf] using hpos
    have hnn : pos d (k + 1 + 1) = (x, y - 2) := by
      rw [hn, hdn] at hpos'
      simp only [stepOf] at hpos'
      calc
        pos d (k + 1 + 1) = (x, y - 1) + (0, -1) := hpos'
        _ = (x, y - 2) := by ext <;> simp <;> omega
    constructor
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [leftCell, hd, hdn, hp, hn]
    · intro hedge
      simp [leftCell, hd, hdn, hp, hn] at hedge
      ring_nf at hedge
      have he : s((![x, y - 1] : Site 2), ![x + 1, y - 1]) ∈
          (imageGraph (walkP d hclosed hsimple)).edgeSet := by
        change sharedPrimalEdge ![x, -1 + y] ![x, -2 + y] ∈ _ at hedge
        rw [show -2 + y = (-1 + y) - 1 by ring] at hedge
        rw [sharedPrimalEdge_bottom] at hedge
        simpa only [faceCorner00, faceCorner10, sub_eq_add_neg, add_comm] using hedge
      have ha : (imageGraph (walkP d hclosed hsimple)).Adj
          ![x, y - 1] ![x + 1, y - 1] := by rwa [← SimpleGraph.mem_edgeSet]
      rcases (imageGraph_adj_pos_iff d hclosed hsimple (k + 1)
        ![x + 1, y - 1]).mp (by simpa [posSite, hn] using ha) with h | h
      · have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [posSite, hp] at h0 h1
      · have h0 := congrFun h 0; have h1 := congrFun h 1
        simp [posSite, hnn] at h0 h1


theorem leftCell_parity_succ (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (k : Fin (m + 3)) :
    rayParity d (leftCell d k).1 (leftCell d k).2 =
      rayParity d (leftCell d (k + 1)).1 (leftCell d (k + 1)).2 := by
  rcases hreflexfree k with hs | hl
  · have hstraight : d (k + 1) = d k := sub_eq_zero.mp hs
    have hadj := leftCell_faceAdj_of_straight d hclosed hsimple k hstraight
    simpa only [cellFace_zero, cellFace_one] using
      rayParity_eq_of_faceAdj d hclosed hsimple hadj
  · have hpos := pos_succ d hclosed k
    have hnext : d (k + 1) = d k + 1 := by
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hl)
    generalize hdk : d k = a
    fin_cases a
    all_goals
      rw [hdk] at hpos hnext
      simp only [stepOf] at hpos
      simp [leftCell, hdk, hnext, hpos] <;> ring_nf


theorem leftCell_parity_eq_of_reachable (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    {i j : Fin (m + 3)} (hreach : (cycleGraph (m + 3)).Reachable i j) :
    rayParity d (leftCell d i).1 (leftCell d i).2 =
      rayParity d (leftCell d j).1 (leftCell d j).2 := by
  obtain ⟨w⟩ := hreach
  induction w with
  | nil => rfl
  | @cons a b c hab p ih =>
      have hab' : rayParity d (leftCell d a).1 (leftCell d a).2 =
          rayParity d (leftCell d b).1 (leftCell d b).2 := by
        rw [cycleGraph_adj] at hab
        rcases hab with hab | hab
        · have ha : a = b + 1 := by
            simpa [add_comm] using sub_eq_iff_eq_add.mp hab
          rw [ha]
          exact (leftCell_parity_succ d hclosed hsimple hreflexfree b).symm
        · have hb : b = a + 1 := by
            simpa [add_comm] using sub_eq_iff_eq_add.mp hab
          rw [hb]
          exact leftCell_parity_succ d hclosed hsimple hreflexfree a
      exact hab'.trans ih



theorem leftCell_parity_one (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (k : Fin (m + 3)) :
    rayParity d (leftCell d k).1 (leftCell d k).2 = 1 := by
  let M := lexInteriorIndex d hclosed hsimple hreflexfree
  have hspec := lexInteriorIndex_spec d hclosed hsimple hreflexfree
  have hdir : d (M - 1) = 1 := hspec.1
  have hpos := pos_pred d hclosed M
  rw [hdir] at hpos
  simp only [stepOf] at hpos
  have hanchor : rayParity d (leftCell d (M - 1)).1 (leftCell d (M - 1)).2 = 1 := by
    have hp := hspec.2.2
    simp only [leftCell, hdir]
    have hx := congrArg Prod.fst hpos
    have hy := congrArg Prod.snd hpos
    simp at hx hy
    rw [show (pos d (M - 1)).1 - 1 = (pos d M).1 - 1 by omega,
      show (pos d (M - 1)).2 = (pos d M).2 - 1 by omega]
    exact hp
  have hreach : (cycleGraph (m + 3)).Reachable k (M - 1) :=
    cycleGraph_connected k (M - 1)
  exact (leftCell_parity_eq_of_reachable d hclosed hsimple hreflexfree hreach).trans hanchor


theorem leftCell_mem_interiorCells (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (k : Fin (m + 3)) :
    leftCell d k ∈ interiorCells d hclosed hsimple hreflexfree := by
  rw [mem_interiorCells_iff_rayParity]
  exact leftCell_parity_one d hclosed hsimple hreflexfree k


theorem walkRegion_flanking_not_reachable (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (k : Fin (m + 3)) {f g : Site 2}
    (hlat : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(posSite d k, posSite d (k + 1))) :
    ¬ (walkRegionGraph d hclosed hsimple).Reachable f g := by
  let P := walkP d hclosed hsimple
  have hev : jcx_IsEven P.G := by
    intro v
    dsimp [P, walkP, walkSubgraph] at v ⊢
    have hne : v - 1 ≠ v + 1 := by
      intro heq
      have hdeg := cycleGraph_degree_three_le (n := m) (v := v)
      rw [cycleGraph_degree_two_le] at hdeg
      simp [heq] at hdeg
    rw [cycleGraph_neighborSet (n := m + 1), Set.ncard_pair hne]
    exact even_two
  letI : DecidableRel P.G.Adj := Classical.decRel _
  have hcontour : jce_ClosedContour (jei_pushGraph P P.G).edgeSet :=
    jcx_pushGraph_closedContour P P.G le_rfl hev
  have hwall : sharedPrimalEdge f g ∈ (jei_pushGraph P P.G).edgeSet := by
    rw [jei_pushGraph_G]
    rw [hshared]
    exact walkEdge_mem_imageGraph d hclosed hsimple k
  have hwallFin : sharedPrimalEdge f g ∈
      (jei_pushGraph_edgeSet_finite P P.G).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hwall
  have hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f g) (jei_pushGraph_edgeSet_finite P P.G).toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
    rw [Finset.insert_eq_of_mem hwallFin]
    simpa only [Set.Finite.coe_toFinset] using hcontour
  have hsep := jwc_syncMerge_of_closedContour P P.G le_rfl hlat hcc
  rw [jei_pushGraph_G] at hsep
  have hnotEdge : s(f, g) ∉ (walkRegionGraph d hclosed hsimple).edgeSet := by
    rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    rintro ⟨_, hn⟩
    apply hn
    rw [hshared]
    exact walkEdge_mem_imageGraph d hclosed hsimple k
  have hdel : (walkRegionGraph d hclosed hsimple).deleteEdges {s(f, g)} =
      walkRegionGraph d hclosed hsimple := by
    apply SimpleGraph.deleteEdges_eq_self.mpr
    rw [Set.disjoint_singleton_right]
    exact hnotEdge
  rw [hdel] at hsep
  exact hsep


theorem left_right_flanking (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin (m + 3)) :
    (hypercubicLattice 2).Adj (cellFace (leftCell d k)) (cellFace (rightCell d k)) ∧
      sharedPrimalEdge (cellFace (leftCell d k)) (cellFace (rightCell d k)) =
        s(posSite d k, posSite d (k + 1)) := by
  have hpos := pos_succ d hclosed k
  generalize hp : pos d k = p at hpos
  obtain ⟨x, y⟩ := p
  generalize hd : d k = a
  fin_cases a
  · have hn : pos d (k + 1) = (x + 1, y) := by simpa [hp, hd, stepOf] using hpos
    constructor
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [leftCell, rightCell, hp, hd]
    · simp [leftCell, rightCell, hd, hp, hn]
      change sharedPrimalEdge ![x, y] ![x, y - 1] = _
      rw [sharedPrimalEdge_bottom]
      simp only [faceCorner00, faceCorner10]
      apply Sym2.eq_iff.mpr
      left
      constructor <;> funext i <;> fin_cases i <;> simp [posSite, hp, hn]
  · have hn : pos d (k + 1) = (x, y + 1) := by simpa [hp, hd, stepOf] using hpos
    constructor
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [leftCell, rightCell, hp, hd]
    · simp [leftCell, rightCell, hd, hp, hn]
      change sharedPrimalEdge ![x - 1, y] ![x, y] = _
      have hsp := sharedPrimalEdge_right (x - 1) y
      ring_nf at hsp
      rw [show x - 1 = -1 + x by ring]
      rw [hsp]
      simp only [faceCorner10, faceCorner11]
      apply Sym2.eq_iff.mpr
      left
      constructor <;> funext i <;> fin_cases i <;> simp [posSite, hp, hn]
  · have hn : pos d (k + 1) = (x - 1, y) := by simpa [hp, hd, stepOf] using hpos
    constructor
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [leftCell, rightCell, hp, hd]
    · simp [leftCell, rightCell, hd, hp, hn]
      change sharedPrimalEdge ![x - 1, y - 1] ![x - 1, y] = _
      have hsp := sharedPrimalEdge_top (x - 1) (y - 1)
      ring_nf at hsp
      rw [show x - 1 = -1 + x by ring, show y - 1 = -1 + y by ring]
      rw [hsp]
      simp only [faceCorner01, faceCorner11]
      apply Sym2.eq_iff.mpr
      right
      constructor <;> funext i <;> fin_cases i <;> simp [posSite, hp, hn] <;> ring
  · have hn : pos d (k + 1) = (x, y - 1) := by simpa [hp, hd, stepOf] using hpos
    constructor
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [leftCell, rightCell, hp, hd]
    · simp [leftCell, rightCell, hd, hp, hn]
      change sharedPrimalEdge ![x, y - 1] ![x - 1, y - 1] = _
      rw [sharedPrimalEdge_left]
      simp only [faceCorner00, faceCorner01]
      apply Sym2.eq_iff.mpr
      right
      constructor <;> funext i <;> fin_cases i <;> simp [posSite, hp, hn]


theorem rightCell_not_mem_interiorCells (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (k : Fin (m + 3)) :
    rightCell d k ∉ interiorCells d hclosed hsimple hreflexfree := by
  intro hr
  have hl := leftCell_mem_interiorCells d hclosed hsimple hreflexfree k
  rw [mem_interiorCells] at hl hr
  have hreach := (innerComponent d hclosed hsimple hreflexfree).reachable_of_mem_supp hl hr
  obtain ⟨hlat, hshared⟩ := left_right_flanking d hclosed k
  exact walkRegion_flanking_not_reachable d hclosed hsimple k hlat hshared hreach


theorem cornerCount_eq_indicators (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    cornerCount S v =
      (if v ∈ S then 1 else 0) +
      (if (v.1 - 1, v.2) ∈ S then 1 else 0) +
      (if (v.1, v.2 - 1) ∈ S then 1 else 0) +
      (if (v.1 - 1, v.2 - 1) ∈ S then 1 else 0) := by
  obtain ⟨x, y⟩ := v
  rw [cornerCount_eq_inter]
  have h := card_inter_eq_sum S
    ({(x, y), (x - 1, y), (x, y - 1), (x - 1, y - 1)} : Finset (ℤ × ℤ))
  rw [
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton, Prod.mk.injEq]; omega),
    Finset.sum_singleton] at h
  have h' : ((S ∩
        ({(x, y), (x - 1, y), (x, y - 1), (x - 1, y - 1)} : Finset (ℤ × ℤ))).card : ℤ) =
      (if (x, y) ∈ S then (1 : ℤ) else 0) +
      (if (x - 1, y) ∈ S then 1 else 0) +
      (if (x, y - 1) ∈ S then 1 else 0) +
      (if (x - 1, y - 1) ∈ S then 1 else 0) := by
    linarith [h]
  exact_mod_cast h'



theorem cornerCount_at_walkVertex (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (k : Fin (m + 3)) :
    cornerCount (interiorCells d hclosed hsimple hreflexfree) (pos d (k + 1)) =
      if d (k + 1) - d k = 1 then 1 else 2 := by
  let S := interiorCells d hclosed hsimple hreflexfree
  change cornerCount S (pos d (k + 1)) = _
  have hlk : leftCell d k ∈ S :=
    leftCell_mem_interiorCells d hclosed hsimple hreflexfree k
  have hl1 : leftCell d (k + 1) ∈ S :=
    leftCell_mem_interiorCells d hclosed hsimple hreflexfree (k + 1)
  have hrk : rightCell d k ∉ S :=
    rightCell_not_mem_interiorCells d hclosed hsimple hreflexfree k
  have hr1 : rightCell d (k + 1) ∉ S :=
    rightCell_not_mem_interiorCells d hclosed hsimple hreflexfree (k + 1)
  have hpos := pos_succ d hclosed k
  generalize hp : pos d k = p at hpos
  obtain ⟨x, y⟩ := p
  rcases hreflexfree k with hs | ht
  · have hdn : d (k + 1) = d k := sub_eq_zero.mp hs
    have hnot : ¬ d (k + 1) - d k = 1 := by rw [hs]; decide
    rw [if_neg hnot]
    generalize hd : d k = a
    fin_cases a
    · have hn : pos d (k + 1) = (x + 1, y) := by simpa [hp, hd, stepOf] using hpos
      simp [leftCell, rightCell, hd, hdn, hp, hn] at hlk hl1 hrk hr1
      rw [cornerCount_eq_indicators S (pos d (k + 1)), hn]
      simp [hlk, hl1, hrk, hr1]
    · have hn : pos d (k + 1) = (x, y + 1) := by simpa [hp, hd, stepOf] using hpos
      simp [leftCell, rightCell, hd, hdn, hp, hn] at hlk hl1 hrk hr1
      rw [cornerCount_eq_indicators S (pos d (k + 1)), hn]
      simp [hlk, hl1, hrk, hr1]
    · have hn : pos d (k + 1) = (x - 1, y) := by simpa [hp, hd, stepOf] using hpos
      simp [leftCell, rightCell, hd, hdn, hp, hn] at hlk hl1 hrk hr1
      rw [cornerCount_eq_indicators S (pos d (k + 1)), hn]
      simp [hlk, hl1, hrk, hr1]
    · have hn : pos d (k + 1) = (x, y - 1) := by simpa [hp, hd, stepOf] using hpos
      simp [leftCell, rightCell, hd, hdn, hp, hn] at hlk hl1 hrk hr1
      rw [cornerCount_eq_indicators S (pos d (k + 1)), hn]
      simp [hlk, hl1, hrk, hr1]
  · rw [if_pos ht]
    have hdn : d (k + 1) = d k + 1 := by
      simpa [add_comm] using (sub_eq_iff_eq_add.mp ht)
    have hnp : ¬ pinchAt S (pos d (k + 1)) :=
      not_pinchAt_interiorCells d hclosed hsimple hreflexfree (pos d (k + 1))
    generalize hd : d k = a
    fin_cases a
    · have hn : pos d (k + 1) = (x + 1, y) := by simpa [hp, hd, stepOf] using hpos
      simp [leftCell, rightCell, hd, hdn, hp, hn] at hlk hl1 hrk hr1
      have hfour : ((x + 1, y - 1) : ℤ × ℤ) ∉ S := by
        intro hf
        apply hnp
        rw [hn]
        unfold pinchAt
        try ring_nf at hl1
        try ring_nf at hrk
        try ring_nf at hr1
        try ring_nf at hf
        try ring_nf
        tauto
      rw [cornerCount_eq_indicators S (pos d (k + 1)), hn]
      try ring_nf at hl1
      try ring_nf at hrk
      try ring_nf at hr1
      try ring_nf at hfour
      try ring_nf
      simp [hl1, hrk, hr1, hfour]
    · have hn : pos d (k + 1) = (x, y + 1) := by simpa [hp, hd, stepOf] using hpos
      simp [leftCell, rightCell, hd, hdn, hp, hn] at hlk hl1 hrk hr1
      have hfour : ((x, y + 1) : ℤ × ℤ) ∉ S := by
        intro hf
        apply hnp
        rw [hn]
        unfold pinchAt
        try ring_nf at hl1
        try ring_nf at hrk
        try ring_nf at hr1
        try ring_nf at hf
        try ring_nf
        tauto
      rw [cornerCount_eq_indicators S (pos d (k + 1)), hn]
      try ring_nf at hl1
      try ring_nf at hrk
      try ring_nf at hr1
      try ring_nf at hfour
      try ring_nf
      simp [hl1, hrk, hr1, hfour]
    · have hn : pos d (k + 1) = (x - 1, y) := by simpa [hp, hd, stepOf] using hpos
      simp [leftCell, rightCell, hd, hdn, hp, hn] at hlk hl1 hrk hr1
      have hfour : ((x - 2, y) : ℤ × ℤ) ∉ S := by
        intro hf
        apply hnp
        rw [hn]
        unfold pinchAt
        try ring_nf at hl1
        try ring_nf at hrk
        try ring_nf at hr1
        try ring_nf at hf
        try ring_nf
        tauto
      rw [cornerCount_eq_indicators S (pos d (k + 1)), hn]
      try ring_nf at hl1
      try ring_nf at hrk
      try ring_nf at hr1
      try ring_nf at hfour
      try ring_nf
      simp [hl1, hrk, hr1, hfour]
    · have hn : pos d (k + 1) = (x, y - 1) := by simpa [hp, hd, stepOf] using hpos
      simp [leftCell, rightCell, hd, hdn, hp, hn] at hlk hl1 hrk hr1
      have hfour : ((x - 1, y - 2) : ℤ × ℤ) ∉ S := by
        intro hf
        apply hnp
        rw [hn]
        unfold pinchAt
        try ring_nf at hl1
        try ring_nf at hrk
        try ring_nf at hr1
        try ring_nf at hf
        try ring_nf
        tauto
      rw [cornerCount_eq_indicators S (pos d (k + 1)), hn]
      try ring_nf at hl1
      try ring_nf at hrk
      try ring_nf at hr1
      try ring_nf at hfour
      try ring_nf
      simp [hl1, hrk, hr1, hfour]



theorem cornerWeight_zero_of_not_walkVertex (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (v : ℤ × ℤ) (hv : ∀ k : Fin (m + 3), pos d k ≠ v) :
    cornerWeight (cornerCount (interiorCells d hclosed hsimple hreflexfree) v) = 0 := by
  let S := interiorCells d hclosed hsimple hreflexfree
  change cornerWeight (cornerCount S v) = _
  obtain ⟨x, y⟩ := v
  have hc := rayParity_const_of_not_vertex d hclosed x y hv
  by_cases h0 : rayParity d x y = 1
  · have hNE : (x, y) ∈ S :=
      (mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree (x, y)).mpr h0
    have hNW : (x - 1, y) ∈ S :=
      (mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree (x - 1, y)).mpr
        (hc.1.trans h0)
    have hSE : (x, y - 1) ∈ S :=
      (mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree (x, y - 1)).mpr
        (hc.2.1.trans h0)
    have hSW : (x - 1, y - 1) ∈ S :=
      (mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree (x - 1, y - 1)).mpr
        (hc.2.2.trans h0)
    rw [cornerCount_eq_indicators]
    simp [hNE, hNW, hSE, hSW, cornerWeight]
  · have hNE : (x, y) ∉ S := by
      intro h; exact h0 ((mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree _).mp h)
    have hNW : (x - 1, y) ∉ S := by
      intro h
      exact h0 (hc.1.symm.trans
        ((mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree _).mp h))
    have hSE : (x, y - 1) ∉ S := by
      intro h
      exact h0 (hc.2.1.symm.trans
        ((mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree _).mp h))
    have hSW : (x - 1, y - 1) ∉ S := by
      intro h
      exact h0 (hc.2.2.symm.trans
        ((mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree _).mp h))
    rw [cornerCount_eq_indicators]
    simp [hNE, hNW, hSE, hSW, cornerWeight]


theorem cornerWeight_at_walkVertex (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (k : Fin (m + 3)) :
    cornerWeight
        (cornerCount (interiorCells d hclosed hsimple hreflexfree) (pos d (k + 1))) =
      if d (k + 1) - d k = 1 then 1 else 0 := by
  rw [cornerCount_at_walkVertex d hclosed hsimple hreflexfree k]
  by_cases ht : d (k + 1) - d k = 1 <;> simp [ht, cornerWeight]



theorem cornerDiff_interiorCells_eq_cc (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cornerDiff (interiorCells d hclosed hsimple hreflexfree) = (cc d : ℤ) := by
  let S := interiorCells d hclosed hsimple hreflexfree
  let V := cellVerts S
  let W := Finset.univ.image (fun k : Fin (m + 3) => pos d (k + 1))
  let w : ℤ × ℤ → ℤ := fun v => cornerWeight (cornerCount S v)
  have hVunion : ∑ v ∈ V, w v = ∑ v ∈ V ∪ W, w v := by
    apply Finset.sum_subset Finset.subset_union_left
    intro v _ hvV
    have hc : cornerCount S v = 0 := by
      by_contra hne
      exact hvV ((cornerCount_pos_iff_mem S v).mp (Nat.pos_of_ne_zero hne))
    simp [w, hc, cornerWeight]
  have hWunion : ∑ v ∈ W, w v = ∑ v ∈ V ∪ W, w v := by
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hvW
    apply cornerWeight_zero_of_not_walkVertex d hclosed hsimple hreflexfree v
    intro k hk
    apply hvW
    apply Finset.mem_image.mpr
    refine ⟨k - 1, Finset.mem_univ _, ?_⟩
    simpa using hk
  rw [cornerDiff_eq_sum]
  change ∑ v ∈ V, w v = _
  rw [hVunion, ← hWunion]
  change (∑ v ∈ Finset.univ.image (fun k : Fin (m + 3) => pos d (k + 1)), w v) = _
  have hinj : ∀ a ∈ (Finset.univ : Finset (Fin (m + 3))), ∀ b ∈ Finset.univ,
      pos d (a + 1) = pos d (b + 1) → a = b := by
    intro a _ b _ hab
    exact (Equiv.addRight (1 : Fin (m + 3))).injective (hsimple hab)
  rw [Finset.sum_image hinj]
  apply Eq.trans (Finset.sum_congr rfl (fun k _ =>
    cornerWeight_at_walkVertex d hclosed hsimple hreflexfree k))
  rw [Finset.sum_boole]
  rfl

end StatMech.Onsager.WalkCellBoundary

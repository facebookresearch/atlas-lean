/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.WalkCellRegion
import Code.Onsager.CellGaussBonnetGlobal

namespace StatMech.Onsager.WalkCellLocal

open Finset SimpleGraph Set
open StatMech.Lattice
open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.JedBridge StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.CellCount StatMech.Onsager.CellEuler StatMech.Onsager.CellPinch

section Walk

variable {m : ℕ}
variable (d : Fin (m + 3) → Fin 4)
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)

local notation "S" => interiorCells d hclosed hsimple hreflexfree
local notation "P" => walkP d hclosed hsimple
local notation "R" => walkRegionGraph d hclosed hsimple


theorem sharedPrimalEdge_mem_of_membership_diff (p q : ℤ × ℤ)
    (hlat : (hypercubicLattice 2).Adj (cellFace p) (cellFace q))
    (hdiff : (p ∈ S ∧ q ∉ S) ∨ (q ∈ S ∧ p ∉ S)) :
    sharedPrimalEdge (cellFace p) (cellFace q) ∈ (imageGraph P).edgeSet := by
  by_contra hedge
  have hadj : (walkRegionGraph d hclosed hsimple).Adj (cellFace p) (cellFace q) :=
    ⟨hlat, hedge⟩
  have hpar := rayParity_eq_of_faceAdj d hclosed hsimple hadj
  have hp := mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree p
  have hq := mem_interiorCells_iff_rayParity d hclosed hsimple hreflexfree q
  rcases hdiff with ⟨hpS, hqS⟩ | ⟨hqS, hpS⟩
  · have hp1 := hp.mp hpS
    change rayParity d p.1 p.2 = rayParity d q.1 q.2 at hpar
    exact hqS (hq.mpr (hpar ▸ hp1))
  · have hq1 := hq.mp hqS
    change rayParity d p.1 p.2 = rayParity d q.1 q.2 at hpar
    exact hpS (hp.mpr (hpar.trans hq1))



theorem pinch_four_edges_impossible (x y : ℤ)
    (hU : sharedPrimalEdge (cellFace (x, y)) (cellFace (x - 1, y)) ∈
      (imageGraph P).edgeSet)
    (hR : sharedPrimalEdge (cellFace (x, y)) (cellFace (x, y - 1)) ∈
      (imageGraph P).edgeSet)
    (hL : sharedPrimalEdge (cellFace (x - 1, y)) (cellFace (x - 1, y - 1)) ∈
      (imageGraph P).edgeSet) : False := by
  have hU' : s((![x, y] : Site 2), ![x, y + 1]) ∈ (imageGraph P).edgeSet := by
    change sharedPrimalEdge ![x, y] ![x - 1, y] ∈ _ at hU
    rw [sharedPrimalEdge_left] at hU
    simpa [faceCorner00, faceCorner01] using hU
  have hR' : s((![x, y] : Site 2), ![x + 1, y]) ∈ (imageGraph P).edgeSet := by
    change sharedPrimalEdge ![x, y] ![x, y - 1] ∈ _ at hR
    rw [sharedPrimalEdge_bottom] at hR
    simpa [faceCorner00, faceCorner10] using hR
  have hL' : s((![x - 1, y] : Site 2), ![x, y]) ∈ (imageGraph P).edgeSet := by
    change sharedPrimalEdge ![x - 1, y] ![x - 1, y - 1] ∈ _ at hL
    rw [sharedPrimalEdge_bottom] at hL
    simpa [faceCorner00, faceCorner10] using hL
  have aU : (imageGraph P).Adj ![x, y] ![x, y + 1] := by
    rwa [← SimpleGraph.mem_edgeSet]
  have aR : (imageGraph P).Adj ![x, y] ![x + 1, y] := by
    rwa [← SimpleGraph.mem_edgeSet]
  have aL : (imageGraph P).Adj ![x, y] ![x - 1, y] := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.eq_swap]
    exact hL'
  change (∃ i j : Fin (m + 3), (cycleGraph (m + 3)).Adj i j ∧
      posSite d i = ![x, y] ∧ posSite d j = ![x, y + 1]) at aU
  obtain ⟨k, j, -, hk, -⟩ := aU
  have cU := (imageGraph_adj_pos_iff d hclosed hsimple k ![x, y + 1]).mp (by rwa [hk])
  have cR := (imageGraph_adj_pos_iff d hclosed hsimple k ![x + 1, y]).mp (by rwa [hk])
  have cL := (imageGraph_adj_pos_iff d hclosed hsimple k ![x - 1, y]).mp (by rwa [hk])
  have neUR : (![x, y + 1] : Site 2) ≠ ![x + 1, y] := by
    intro h
    have h0 : x = x + 1 := by simpa using congrFun h 0
    omega
  have neUL : (![x, y + 1] : Site 2) ≠ ![x - 1, y] := by
    intro h
    have h0 : x = x - 1 := by simpa using congrFun h 0
    omega
  have neRL : (![x + 1, y] : Site 2) ≠ ![x - 1, y] := by
    intro h
    have h0 : x + 1 = x - 1 := by simpa using congrFun h 0
    omega
  rcases cU with cU | cU
  · rcases cR with cR | cR
    · exact neUR (cU.trans cR.symm)
    · rcases cL with cL | cL
      · exact neUL (cU.trans cL.symm)
      · exact neRL (cR.trans cL.symm)
  · rcases cR with cR | cR
    · rcases cL with cL | cL
      · exact neRL (cR.trans cL.symm)
      · exact neUL (cU.trans cL.symm)
    · exact neUR (cU.trans cR.symm)


theorem not_pinchAt_interiorCells (v : ℤ × ℤ) : ¬ pinchAt S v := by
  rintro (hpin | hpin)
  all_goals
    obtain ⟨x, y⟩ := v
    simp only at hpin
  · obtain ⟨hne, hsw, hnw, hse⟩ := hpin
    have dUNW : (((x, y) : ℤ × ℤ) ∈ S ∧ (x - 1, y) ∉ S) ∨
        ((x - 1, y) ∈ S ∧ (x, y) ∉ S) := Or.inl ⟨hne, hnw⟩
    have dRSE : (((x, y) : ℤ × ℤ) ∈ S ∧ (x, y - 1) ∉ S) ∨
        ((x, y - 1) ∈ S ∧ (x, y) ∉ S) := Or.inl ⟨hne, hse⟩
    have dLSW : (((x - 1, y) : ℤ × ℤ) ∈ S ∧ (x - 1, y - 1) ∉ S) ∨
        ((x - 1, y - 1) ∈ S ∧ (x - 1, y) ∉ S) := Or.inr ⟨hsw, hnw⟩
    have dDSE : (((x, y - 1) : ℤ × ℤ) ∈ S ∧ (x - 1, y - 1) ∉ S) ∨
        ((x - 1, y - 1) ∈ S ∧ (x, y - 1) ∉ S) := Or.inr ⟨hsw, hse⟩
    have hU := sharedPrimalEdge_mem_of_membership_diff d hclosed hsimple hreflexfree
      (x, y) (x - 1, y) (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num) dUNW
    have hR := sharedPrimalEdge_mem_of_membership_diff d hclosed hsimple hreflexfree
      (x, y) (x, y - 1) (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num) dRSE
    have hL := sharedPrimalEdge_mem_of_membership_diff d hclosed hsimple hreflexfree
      (x - 1, y) (x - 1, y - 1)
      (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num) dLSW
    exact pinch_four_edges_impossible d hclosed hsimple x y hU hR hL
  · obtain ⟨hnw, hse, hne, hsw⟩ := hpin
    have dUNW : (((x, y) : ℤ × ℤ) ∈ S ∧ (x - 1, y) ∉ S) ∨
        ((x - 1, y) ∈ S ∧ (x, y) ∉ S) := Or.inr ⟨hnw, hne⟩
    have dRSE : (((x, y) : ℤ × ℤ) ∈ S ∧ (x, y - 1) ∉ S) ∨
        ((x, y - 1) ∈ S ∧ (x, y) ∉ S) := Or.inr ⟨hse, hne⟩
    have dLSW : (((x - 1, y) : ℤ × ℤ) ∈ S ∧ (x - 1, y - 1) ∉ S) ∨
        ((x - 1, y - 1) ∈ S ∧ (x - 1, y) ∉ S) := Or.inl ⟨hnw, hsw⟩
    have hU := sharedPrimalEdge_mem_of_membership_diff d hclosed hsimple hreflexfree
      (x, y) (x - 1, y) (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num) dUNW
    have hR := sharedPrimalEdge_mem_of_membership_diff d hclosed hsimple hreflexfree
      (x, y) (x, y - 1) (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num) dRSE
    have hL := sharedPrimalEdge_mem_of_membership_diff d hclosed hsimple hreflexfree
      (x - 1, y) (x - 1, y - 1)
      (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num) dLSW
    exact pinch_four_edges_impossible d hclosed hsimple x y hU hR hL


theorem pinchCount_interiorCells_eq_zero : pinchCount S = 0 := by
  unfold pinchCount
  apply Finset.sum_eq_zero
  intro v _
  rw [pinchW, if_neg (not_pinchAt_interiorCells d hclosed hsimple hreflexfree v)]

end Walk

end StatMech.Onsager.WalkCellLocal

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Mathlib
import Code.Walls.bc67supervertex
import Code.Percolation.GridBoxConnected

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

namespace StatMech.Walls








def bff_BoxAllOpen (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) : Prop :=
  ∀ e ∈ boxEdges 2 n, ω e = true





theorem bff_allOpen_box_connected {ω : ConfigSpace (Sym2 (Site 2))} {n : ℕ}
    (h : bff_BoxAllOpen ω n) {x y : Site 2}
    (hx : x ∈ Lattice.box 2 n) (hy : y ∈ Lattice.box 2 n) :
    Lattice.Connected 2 ω x y := by
  have heq : forceOpenFinset (boxEdges 2 n) ω = ω := by
    funext e
    by_cases he : e ∈ boxEdges 2 n
    · rw [forceOpenFinset_of_mem he, h e he]
    · rw [forceOpenFinset_of_notMem he]
  have hconn := box_allOpen_connected (n := n) ω hx hy
  rwa [heq] at hconn








theorem bff_upperLines_box_edge_mem {L : ℕ} (hL : 1 ≤ L) :
    s(bc57_pt 0 0, bc57_pt 1 0) ∈ boxEdges 2 L := by
  have hx0 : (bc57_pt 0 0 : Site 2) ∈ Lattice.box 2 L := by
    simp only [Lattice.box, Set.mem_setOf_eq]
    intro i; fin_cases i <;> simp [bc57_pt]
  have hx1 : (bc57_pt 1 0 : Site 2) ∈ Lattice.box 2 L := by
    simp only [Lattice.box, Set.mem_setOf_eq]
    intro i; fin_cases i <;> simp [bc57_pt] <;> omega
  have hadj : (hypercubicLattice 2).Adj (bc57_pt 0 0) (bc57_pt 1 0) := by
    simpa using bc57_pt_adj (0 : ℤ) 0
  exact mk_mem_boxEdges hx0 hx1 hadj



theorem bff_upperLines_box_edge_closed :
    bc60_upperLines s(bc57_pt 0 0, bc57_pt 1 0) = false := by
  rcases Bool.eq_false_or_eq_true (bc60_upperLines s(bc57_pt 0 0, bc57_pt 1 0)) with h | h
  · exfalso
    have h1 := (bc60_open_edge_heights h).1
    rw [bc57_pt_snd] at h1
    exact absurd h1 (by norm_num)
  · exact h



theorem bff_upperLines_box_not_allOpen {L : ℕ} (hL : 1 ≤ L) :
    ¬ bff_BoxAllOpen bc60_upperLines L := by
  intro hall
  have hopen := hall _ (bff_upperLines_box_edge_mem hL)
  rw [bff_upperLines_box_edge_closed] at hopen
  exact absurd hopen (by decide)












theorem bff_genuine_trif_with_non_allOpen_box {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
      ¬ bff_BoxAllOpen bc60_upperLines L :=
  ⟨bc67_upperLines_is_G_n_trifurcation hL,
   bff_upperLines_box_not_allOpen (le_trans (by norm_num) hL)⟩

#check @bff_allOpen_box_connected
#check @bff_upperLines_box_not_allOpen
#check @bff_genuine_trif_with_non_allOpen_box

#print axioms bff_genuine_trif_with_non_allOpen_box
#print axioms bff_allOpen_box_connected
#print axioms bff_upperLines_box_not_allOpen

end StatMech.Walls

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.PlanarFaceGeometric
import Code.Lattice.CrossingParity
import Code.Lattice.JordanEnclosure
import Code.Lattice.WhitneyBridge
import Code.Lattice.JordanBridgeCycle

open SimpleGraph Set

namespace StatMech

namespace Lattice













theorem whc_deleted_le_latticeMinusBarrier (H : SimpleGraph (Site 2)) (f g : Site 2) :
    ((whb_faceRegion H).deleteEdges {s(f, g)}) ≤
      latticeMinusBarrier {v | ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable f v} := by
  intro x y hxy
  rw [latticeMinusBarrier_adj]
  have hwr : (whb_faceRegion H).Adj x y := deleteEdges_le _ hxy
  have hlat : (hypercubicLattice 2).Adj x y := ((whb_faceRegion_adj H x y).mp hwr).1
  refine ⟨hlat, ?_⟩
  rw [bdEdge_mk]
  intro hcon
  simp only [Set.mem_setOf_eq] at hcon
  have hr : ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable x y := hxy.reachable
  by_cases hx : ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable f x
  · exact (hcon.mp hx) (hx.trans hr)
  · exact hx (hcon.mpr (fun h => hx (h.trans hr.symm)))














noncomputable def whc_dualCross (H : SimpleGraph (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ := by
  classical
  exact w.edges.countP (fun e => decide (Sym2.lift ⟨fun a b =>
      sharedPrimalEdge a b ∈ H.edgeSet ∨ sharedPrimalEdge b a ∈ H.edgeSet, by
    intro a b; simp only [eq_iff_iff]; tauto⟩ e))



def whc_isCross (H : SimpleGraph (Site 2)) (a b : Site 2) : Prop :=
  sharedPrimalEdge a b ∈ H.edgeSet ∨ sharedPrimalEdge b a ∈ H.edgeSet

@[simp] theorem whc_dualCross_nil (H : SimpleGraph (Site 2)) (x : Site 2) :
    whc_dualCross H (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical
  simp [whc_dualCross]

open Classical in

theorem whc_dualCross_cons (H : SimpleGraph (Site 2)) {a b c : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) (p : (hypercubicLattice 2).Walk b c) :
    whc_dualCross H (Walk.cons hab p) =
      (if whc_isCross H a b then 1 else 0) + whc_dualCross H p := by
  rw [whc_dualCross, whc_dualCross, SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases h : whc_isCross H a b
  · rw [if_pos (by simp only [Sym2.lift_mk, decide_eq_true_eq]; exact h), if_pos h]; ring
  · rw [if_neg (by simp only [Sym2.lift_mk, decide_eq_true_eq]; exact h), if_neg h]; ring





def whc_CompatColoring (H : SimpleGraph (Site 2)) (φ : Site 2 → Prop) : Prop :=
  ∀ a b, (hypercubicLattice 2).Adj a b → (whc_isCross H a b ↔ (φ a ↔ ¬ φ b))





theorem whc_dualCross_parity (H : SimpleGraph (Site 2)) (φ : Site 2 → Prop)
    (hcompat : whc_CompatColoring H φ) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (whc_dualCross H w) ↔ (φ x ↔ φ y) := by
  classical
  induction w with
  | nil => simp [whc_dualCross]
  | @cons a b c hab p ih =>
    rw [whc_dualCross_cons H hab p]
    by_cases hcr : whc_isCross H a b
    · rw [if_pos hcr, add_comm, Nat.even_add_one, ih]
      have := (hcompat a b hab).mp hcr
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all
    · rw [if_neg hcr, zero_add, ih]
      have := (fun hh => hcr ((hcompat a b hab).mpr hh))
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all















def whc_CutColoring (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) (φ : Site 2 → Prop) : Prop :=
  ∀ a b, (hypercubicLattice 2).Adj a b →
    ((whc_isCross H a b ∨ s(a, b) = s(f0, g0)) ↔ (φ a ↔ ¬ φ b))





theorem whc_deleted_step_preserves (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) {a b : Site 2}
    (hab : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Adj a b) : (φ a ↔ φ b) := by
  have hwr : (whb_faceRegion H).Adj a b := deleteEdges_le _ hab
  have hlat : (hypercubicLattice 2).Adj a b := ((whb_faceRegion_adj H a b).mp hwr).1
  have hnH : sharedPrimalEdge a b ∉ H.edgeSet := ((whb_faceRegion_adj H a b).mp hwr).2
  have hne : s(a, b) ≠ s(f0, g0) := by
    intro heq
    rw [deleteEdges_adj] at hab
    exact hab.2 (by rw [heq]; exact Set.mem_singleton _)
  have hnc : ¬ whc_isCross H a b := by
    rw [whc_isCross]; push Not
    refine ⟨hnH, ?_⟩
    rwa [sharedPrimalEdge_comm_of_adj hlat] at hnH
  have hkey := hcut a b hlat
  have hnflip : ¬ (whc_isCross H a b ∨ s(a, b) = s(f0, g0)) := by
    push Not; exact ⟨hnc, hne⟩
  rw [hkey] at hnflip
  by_cases ha : φ a <;> by_cases hb : φ b <;> simp_all


theorem whc_deleted_walk_preserves (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) {x y : Site 2}
    (w : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Walk x y) : (φ x ↔ φ y) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih => exact (whc_deleted_step_preserves H f0 g0 φ hcut hab).trans ih





theorem whc_deleted_separated (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) (hne : ¬ (φ f0 ↔ φ g0)) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  rintro ⟨w⟩
  exact hne (whc_deleted_walk_preserves H f0 g0 φ hcut w)


























def whc_WhitneyColoringResidue : Prop :=
  ∀ (H : SimpleGraph (Site 2)) (p q f0 g0 : Site 2),
    (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
    (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) →
    ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ ∧
      (H.Reachable p q ↔ ¬ (φ f0 ↔ φ g0)) ∧
      ((φ f0 ↔ φ g0) → ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0)






theorem whc_correctWhitney_of_residue (hres : whc_WhitneyColoringResidue) :
    whb_CorrectWhitney := by
  intro H p q f0 g0 hpq hnpq hfg hshared
  obtain ⟨φ, hcut, htrack, hback⟩ := hres H p q f0 g0 hpq hnpq hfg hshared
  constructor
  · intro hreach
    exact whc_deleted_separated H f0 g0 φ hcut (htrack.mp hreach)
  · intro hsep
    by_contra hnr
    have hsame : (φ f0 ↔ φ g0) := by
      by_contra hdiff
      exact hnr (htrack.mpr hdiff)
    exact hsep (hback hsame)











theorem whc_shared_hstep (a0 a1 b1 : ℤ) :
    sharedPrimalEdge ![a0, a1] ![a0, b1] = s(![a0, max a1 b1], ![a0 + 1, max a1 b1]) := by
  unfold sharedPrimalEdge; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, if_true]



theorem whc_shared_vstep (a0 b0 a1 : ℤ) (h : a0 ≠ b0) :
    sharedPrimalEdge ![a0, a1] ![b0, a1] = s(![max a0 b0, a1], ![max a0 b0, a1 + 1]) := by
  unfold sharedPrimalEdge
  rw [if_neg (by simp only [Matrix.cons_val_zero]; exact h)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]


theorem whc_site_eq_iff (x : Site 2) (c d : ℤ) : x = ![c, d] ↔ x 0 = c ∧ x 1 = d := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> simp_all



macro "whc_prove_inv" : tactic => `(tactic|
  (rename_i a b hab
   have ha : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
   have hb : b = ![b 0, b 1] := by funext i; fin_cases i <;> rfl
   rw [hypercubicLattice_adj, Fin.sum_univ_two] at hab
   by_cases h0 : a 0 = b 0
   · rw [ha, hb, h0, whc_shared_hstep, Sym2.eq_iff, Sym2.eq_iff]
     simp only [whc_site_eq_iff, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
   · have h1 : a 1 = b 1 := by omega
     rw [ha, hb, h1, whc_shared_vstep (a 0) (b 0) (b 1) h0, Sym2.eq_iff, Sym2.eq_iff]
     simp only [whc_site_eq_iff, Matrix.cons_val_zero, Matrix.cons_val_one]; omega))



theorem whc_inv_bottom (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b = s(![(0:ℤ), 0], ![1, 0]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
  whc_prove_inv


theorem whc_inv_right (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b = s(![(1:ℤ), 0], ![1, 1]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
  whc_prove_inv


theorem whc_inv_top (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b = s(![(1:ℤ), 1], ![0, 1]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), 1]) := by
  whc_prove_inv


theorem whc_inv_left (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b = s(![(0:ℤ), 1], ![0, 0]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(-1:ℤ), 0]) := by
  whc_prove_inv












noncomputable def whc_Htest : SimpleGraph (Site 2) :=
  (imageGraph jbc_Pce).deleteEdges {s(![(0:ℤ), 0], ![1, 0])}


def whc_phiWitness : Site 2 → Prop := fun f => f = ![(0:ℤ), 0]

theorem whc_phiWitness_iff (x : Site 2) : whc_phiWitness x ↔ (x 0 = 0 ∧ x 1 = 0) := by
  unfold whc_phiWitness; rw [whc_site_eq_iff]


theorem whc_square_adj_cases {u v : Site 2} (h : (imageGraph jbc_Pce).Adj u v) :
    (u = ![(0:ℤ), 0] ∧ v = ![1, 0]) ∨ (u = ![(1:ℤ), 0] ∧ v = ![0, 0]) ∨
    (u = ![(1:ℤ), 0] ∧ v = ![1, 1]) ∨ (u = ![(1:ℤ), 1] ∧ v = ![1, 0]) ∨
    (u = ![(1:ℤ), 1] ∧ v = ![0, 1]) ∨ (u = ![(0:ℤ), 1] ∧ v = ![1, 1]) ∨
    (u = ![(0:ℤ), 1] ∧ v = ![0, 0]) ∨ (u = ![(0:ℤ), 0] ∧ v = ![0, 1]) := by
  obtain ⟨i, j, hadj, hu, hv⟩ := h
  have hadj' : jbc_cyc4Rel i j = true := hadj
  have hu' : jbc_csq i = u := hu
  have hv' : jbc_csq j = v := hv
  subst hu'; subst hv'
  revert hadj'
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => k.elim0)))) i <;>
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => k.elim0)))) j <;>
    intro hadj' <;> first
      | (exact absurd hadj' (by decide))
      | (simp only [jbc_csq]; tauto)



theorem whc_square_mem_iff (e : Sym2 (Site 2)) :
    e ∈ (imageGraph jbc_Pce).edgeSet ↔
      e = s(![(0:ℤ), 0], ![1, 0]) ∨ e = s(![(1:ℤ), 0], ![1, 1]) ∨
      e = s(![(1:ℤ), 1], ![0, 1]) ∨ e = s(![(0:ℤ), 1], ![0, 0]) := by
  induction e with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · intro h
      rcases whc_square_adj_cases h with
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
        simp only [Sym2.eq_iff] <;> tauto
    · intro h
      obtain ⟨i, j, ha, hb, hc⟩ :
          ∃ x y : Fin 4, jbc_cyc4.Adj x y ∧ jbc_csq x = u ∧ jbc_csq y = v := by
        rcases h with h|h|h|h <;> rw [Sym2.eq_iff] at h <;> rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨0, 1, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨1, 0, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨1, 2, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨2, 1, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨2, 3, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨3, 2, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨3, 0, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨0, 3, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
      exact ⟨i, j, ha, hb, hc⟩



theorem whc_shared_mem_square_iff (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b ∈ (imageGraph jbc_Pce).edgeSet ↔
      (s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) ∨ s(a, b) = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∨
       s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), 1]) ∨ s(a, b) = s(![(0:ℤ), 0], ![(-1:ℤ), 0])) := by
  rw [whc_square_mem_iff, whc_inv_bottom a b hab, whc_inv_right a b hab, whc_inv_top a b hab,
    whc_inv_left a b hab]

theorem whc_Htest_mem (e : Sym2 (Site 2)) :
    e ∈ whc_Htest.edgeSet ↔
      e ∈ (imageGraph jbc_Pce).edgeSet ∧ e ≠ s(![(0:ℤ), 0], ![1, 0]) := by
  unfold whc_Htest
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]



theorem whc_cross_or_bottom_iff (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    (whc_isCross whc_Htest a b ∨ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1])) ↔
      sharedPrimalEdge a b ∈ (imageGraph jbc_Pce).edgeSet := by
  have hsy : sharedPrimalEdge a b = sharedPrimalEdge b a := sharedPrimalEdge_comm_of_adj hab
  unfold whc_isCross
  rw [whc_Htest_mem, whc_Htest_mem, ← hsy]
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact h
    · exact (whc_shared_mem_square_iff a b hab).mpr (Or.inl h)
  · intro h
    by_cases hbot : s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1])
    · right; exact hbot
    · left; left
      exact ⟨h, fun hbadb => hbot ((whc_inv_bottom a b hab).mp hbadb)⟩




theorem whc_cutColoring_witness :
    whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] whc_phiWitness := by
  intro a b hab
  have hadj := hab
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  rw [whc_cross_or_bottom_iff a b hab, whc_shared_mem_square_iff a b hab,
    whc_phiWitness_iff, whc_phiWitness_iff]
  rw [Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff]
  simp only [whc_site_eq_iff]
  set a0 := a 0; set a1 := a 1; set b0 := b 0; set b1 := b 1
  clear_value a0 a1 b0 b1
  clear hab
  have hd : (a0 = b0 ∧ (a1 = b1 + 1 ∨ b1 = a1 + 1)) ∨
      (a1 = b1 ∧ (a0 = b0 + 1 ∨ b0 = a0 + 1)) := by have := hadj; omega
  rcases hd with ⟨rfl, (rfl|rfl)⟩ | ⟨rfl, (rfl|rfl)⟩ <;> omega


theorem whc_Htest_adj_of_square (u v : Site 2) (h : (imageGraph jbc_Pce).Adj u v)
    (hne : s(u, v) ≠ s(![(0:ℤ), 0], ![1, 0])) : whc_Htest.Adj u v := by
  unfold whc_Htest
  rw [deleteEdges_adj, Set.mem_singleton_iff]
  exact ⟨h, hne⟩




theorem whc_Htest_reach_pq : whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] := by
  have sqAdj : ∀ u v : Site 2,
      s(u, v) ∈ (imageGraph jbc_Pce).edgeSet → (imageGraph jbc_Pce).Adj u v :=
    fun u v h => (SimpleGraph.mem_edgeSet _).mp h
  have e1 : whc_Htest.Adj ![(0:ℤ), 0] ![(0:ℤ), 1] :=
    whc_Htest_adj_of_square _ _
      (sqAdj _ _ (by rw [whc_square_mem_iff]; right; right; right; rw [Sym2.eq_iff]; tauto))
      (by rw [ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e2 : whc_Htest.Adj ![(0:ℤ), 1] ![(1:ℤ), 1] :=
    whc_Htest_adj_of_square _ _
      (sqAdj _ _ (by rw [whc_square_mem_iff]; right; right; left; rw [Sym2.eq_iff]; tauto))
      (by rw [ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e3 : whc_Htest.Adj ![(1:ℤ), 1] ![(1:ℤ), 0] :=
    whc_Htest_adj_of_square _ _
      (sqAdj _ _ (by rw [whc_square_mem_iff]; right; left; rw [Sym2.eq_iff]; tauto))
      (by rw [ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  exact (e1.reachable.trans e2.reachable).trans e3.reachable


theorem whc_phiWitness_diff : ¬ (whc_phiWitness ![(0:ℤ), 0] ↔ whc_phiWitness ![(0:ℤ), -1]) := by
  rw [whc_phiWitness_iff, whc_phiWitness_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num










theorem whc_residue_witness :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ whc_Htest.edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    (∃ φ : Site 2 → Prop, whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] φ ∧
      (whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ↔ ¬ (φ ![(0:ℤ), 0] ↔ φ ![(0:ℤ), -1]))) := by
  refine ⟨?_, ?_, ?_, ?_, whc_phiWitness, whc_cutColoring_witness, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [whc_Htest_mem]; push Not; intro _; rw [Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num
  · exact ⟨fun _ => whc_phiWitness_diff, fun _ => whc_Htest_reach_pq⟩
















noncomputable def whc_faithfulRegionCount (P : PlanarZ2Subgraph) : ℕ :=
  Nat.card {c : (whb_faceRegion (imageGraph P)).ConnectedComponent // c.supp.Finite}









def whc_FaithfulDiscreteJordan (P : PlanarZ2Subgraph) : Prop :=
  Nonempty ({c : (whb_faceRegion (imageGraph P)).ConnectedComponent // c.supp.Finite} ≃
    Fin (nullity P.G))







theorem whc_faithful_square_nonempty :
    Nonempty {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite} :=
  ⟨⟨(whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0],
    whb_faceRegion_interior_bounded⟩⟩

end Lattice

end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.WhitneyBridge
import Code.Lattice.WhitneyCorrect
import Code.Lattice.JordanWindingConstruct
import Code.Lattice.JordanKeepDual

open SimpleGraph Set

namespace StatMech

namespace Lattice









def jkr_lineRel (a b : Site 2) : Prop :=
  a 1 = 0 ∧ b 1 = 0 ∧ ¬ ({a 0, b 0} = ({0, 1} : Finset ℤ))



def jkr_lineH : SimpleGraph (Site 2) where
  Adj a b := (hypercubicLattice 2).Adj a b ∧ jkr_lineRel a b
  symm := by
    rintro a b ⟨hadj, h0, h1, hne⟩
    refine ⟨hadj.symm, h1, h0, ?_⟩
    rwa [Finset.pair_comm]
  loopless := ⟨fun a h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem jkr_lineH_adj (a b : Site 2) :
    jkr_lineH.Adj a b ↔ (hypercubicLattice 2).Adj a b ∧
      a 1 = 0 ∧ b 1 = 0 ∧ ¬ ({a 0, b 0} = ({0, 1} : Finset ℤ)) := Iff.rfl



theorem jkr_pair_eq_iff (c d : ℤ) (hne : c ≠ d) :
    ({c, d} = ({0, 1} : Finset ℤ)) ↔ ((c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0)) := by
  constructor
  · intro h
    have hc : c ∈ ({0, 1} : Finset ℤ) := by rw [← h]; simp
    have hd : d ∈ ({0, 1} : Finset ℤ) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [Finset.pair_comm]



theorem jkr_wall_not_mem :
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jkr_lineH.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, jkr_lineH_adj]
  rintro ⟨_, _, _, hne⟩
  exact hne (by decide)



theorem jkr_edge_on_line {a b : Site 2} (h : jkr_lineH.Adj a b) : a 1 = 0 ∧ b 1 = 0 :=
  ⟨h.2.1, h.2.2.1⟩




theorem jkr_edge_x {a b : Site 2} (h : jkr_lineH.Adj a b) :
    (a 0 = b 0 + 1 ∨ b 0 = a 0 + 1) ∧ ¬ ({a 0, b 0} = ({0, 1} : Finset ℤ)) := by
  obtain ⟨hlat, ha1, hb1, hne⟩ := h
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  refine ⟨?_, hne⟩
  rw [ha1, hb1] at hlat
  simp only [sub_self, Int.natAbs_zero, add_zero] at hlat
  omega










theorem jkr_edge_sameSide {a b : Site 2} (h : jkr_lineH.Adj a b) :
    (a 0 ≤ 0 ↔ b 0 ≤ 0) := by
  obtain ⟨hx, hne⟩ := jkr_edge_x h
  by_cases hab : a 0 = b 0
  · rw [hab]
  · rw [jkr_pair_eq_iff (a 0) (b 0) hab] at hne
    push Not at hne
    constructor <;> intro <;> omega


theorem jkr_walk_sameSide {x y : Site 2} (w : jkr_lineH.Walk x y) :
    (x 0 ≤ 0 ↔ y 0 ≤ 0) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih => exact (jkr_edge_sameSide hab).trans ih




theorem jkr_pq_not_reachable : ¬ jkr_lineH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] := by
  rintro ⟨w⟩
  have h := jkr_walk_sameSide w
  simp only [Matrix.cons_val_zero] at h
  omega
















theorem jkr_shared_vstep_line (a : ℤ) :
    sharedPrimalEdge ![a, (0:ℤ)] ![a, -1] = s(![a, (0:ℤ)], ![a + 1, 0]) := by
  rw [whc_shared_hstep a 0 (-1)]
  rw [show max (0:ℤ) (-1) = 0 by norm_num]



theorem jkr_line_seg_mem (a : ℤ) :
    s(![a, (0:ℤ)], ![a + 1, 0]) ∈ jkr_lineH.edgeSet ↔ a ≠ 0 := by
  rw [SimpleGraph.mem_edgeSet, jkr_lineH_adj]
  have hy0 : (![a, (0:ℤ)] : Site 2) 1 = 0 := rfl
  have hy1 : (![a + 1, (0:ℤ)] : Site 2) 1 = 0 := rfl
  have hx0 : (![a, (0:ℤ)] : Site 2) 0 = a := rfl
  have hx1 : (![a + 1, (0:ℤ)] : Site 2) 0 = a + 1 := rfl
  rw [hy0, hy1, hx0, hx1]
  constructor
  · rintro ⟨_, _, _, hne⟩ hzero
    subst hzero
    exact hne (by decide)
  · intro ha
    refine ⟨?_, rfl, rfl, ?_⟩
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega
    · rw [jkr_pair_eq_iff a (a + 1) (by omega)]
      push Not; omega





theorem jkr_deleted_edge_sameSide {a b : Site 2}
    (h : ((whb_faceRegion jkr_lineH).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Adj a b) :
    (0 ≤ a 1 ↔ 0 ≤ b 1) := by
  rw [deleteEdges_adj, Set.mem_singleton_iff] at h
  obtain ⟨hwr, hne⟩ := h
  rw [whb_faceRegion_adj] at hwr
  obtain ⟨hlat, hnH⟩ := hwr
  
  have hlat' := hlat
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat'
  
  by_contra hcross
  
  
  have hcase : (a 0 = b 0 ∧ (a 1 = b 1 + 1 ∨ b 1 = a 1 + 1)) ∨
      (a 1 = b 1 ∧ (a 0 = b 0 + 1 ∨ b 0 = a 0 + 1)) := by omega
  
  rcases hcase with ⟨hx, hy⟩ | ⟨hy, _⟩
  · 
    have hstraddle : (a 1 = 0 ∧ b 1 = -1) ∨ (a 1 = -1 ∧ b 1 = 0) := by
      rcases hy with hy | hy <;> [skip; skip] <;> omega
    
    set a0 := a 0 with ha0
    have hb0 : b 0 = a0 := hx.symm
    
    have ha : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
    have hb : b = ![b 0, b 1] := by funext i; fin_cases i <;> rfl
    by_cases hz : a0 = 0
    · 
      apply hne
      rw [Sym2.eq_iff]
      rcases hstraddle with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
      · left
        rw [ha, hb, ← ha0, hb0, hz, ha1, hb1]
        constructor <;> · funext i; fin_cases i <;> rfl
      · right
        rw [ha, hb, ← ha0, hb0, hz, ha1, hb1]
        constructor <;> · funext i; fin_cases i <;> rfl
    · 
      apply hnH
      rcases hstraddle with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
      · rw [ha, hb, ← ha0, hb0, ha1, hb1, jkr_shared_vstep_line a0]
        exact (jkr_line_seg_mem a0).mpr hz
      · 
        rw [ha, hb, ← ha0, hb0, ha1, hb1]
        rw [show sharedPrimalEdge ![a0, -1] ![a0, (0:ℤ)]
              = sharedPrimalEdge ![a0, (0:ℤ)] ![a0, -1] from ?_]
        · rw [jkr_shared_vstep_line a0]; exact (jkr_line_seg_mem a0).mpr hz
        · rw [whc_shared_hstep a0 (-1) 0, whc_shared_hstep a0 0 (-1),
            show max (-1:ℤ) 0 = 0 by norm_num, show max (0:ℤ) (-1) = 0 by norm_num]
  · 
    exact hcross (by rw [hy])


theorem jkr_deleted_walk_sameSide {x y : Site 2}
    (w : ((whb_faceRegion jkr_lineH).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Walk x y) :
    (0 ≤ x 1 ↔ 0 ≤ y 1) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih => exact (jkr_deleted_edge_sameSide hab).trans ih





theorem jkr_faces_not_reconnect :
    ¬ ((whb_faceRegion jkr_lineH).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  rintro ⟨w⟩
  have h := jkr_deleted_walk_sameSide w
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
  omega










theorem jkr_instance_valid :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jkr_lineH.edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
  refine ⟨?_, jkr_wall_not_mem, ?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num









theorem jkr_keepReconnectResidue_false : ¬ jwn_KeepReconnectResidue := by
  intro hres
  obtain ⟨hpq, hnpq, hfg, hshared⟩ := jkr_instance_valid
  exact jkr_faces_not_reconnect
    (hres jkr_lineH ![(0:ℤ), 0] ![(1:ℤ), 0] ![(0:ℤ), 0] ![(0:ℤ), -1]
      hpq hnpq hfg hshared jkr_pq_not_reachable)














theorem jkr_witness_bot :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    ¬ (⊥ : SimpleGraph (Site 2)).Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] :=
  jwn_witness_square





theorem jkr_witness_square :
    (hypercubicLattice 2).Adj (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) ∧
    s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∉ (jei_pushGraph jbc_Pce ⊥).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∧
    ¬ (jei_pushGraph jbc_Pce ⊥).Reachable (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) ∧
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hna : ¬ (⊥ : SimpleGraph jbc_Pce.V).Adj jbc_v0 jbc_v1 := by
    rw [SimpleGraph.bot_adj]; exact not_false
  have hpq : (hypercubicLattice 2).Adj (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) :=
    jbc_Pce.isSub jbc_Pce_Gadj
  refine ⟨hpq, jkd_wall_not_mem_pushGraph jbc_Pce ⊥ hna,
    jkd_latadj (by rw [Fin.sum_univ_two]; norm_num), jkd_shared_bottom, ?_,
    jkd_witness_square_reach⟩
  rw [jei_push_reachable_iff]; intro h
  rw [SimpleGraph.reachable_bot] at h; exact jbc_v0_ne_v1 h





theorem jkr_witness_ring :
    jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧
    s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉ (jei_pushGraph jkd_ringP ⊥).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧
    ¬ (jei_pushGraph jkd_ringP ⊥).Reachable (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] :=
  jwn_witness_ring












def jkr_FiniteKeepReconnectResidue : Prop :=
  ∀ (H : SimpleGraph (Site 2)) (p q f0 g0 : Site 2),
    H.edgeSet.Finite →
    (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
    (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) →
    ¬ H.Reachable p q →
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0



theorem jkr_finite_of_keepReconnect (hres : jwn_KeepReconnectResidue) :
    jkr_FiniteKeepReconnectResidue :=
  fun H p q f0 g0 _hfin hpq hnpq hfg hshared hnr => hres H p q f0 g0 hpq hnpq hfg hshared hnr




theorem jkr_lineH_edgeSet_infinite : jkr_lineH.edgeSet.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => s(![(n : ℤ) + 1, (0:ℤ)], ![(n : ℤ) + 1 + 1, 0])) ?_ ?_
  · intro m n hmn
    simp only at hmn
    rw [Sym2.eq_iff] at hmn
    rcases hmn with ⟨h, _⟩ | ⟨h, hb⟩
    · rw [site2_eq] at h
      have : (m : ℤ) = (n : ℤ) := by omega
      exact_mod_cast this
    · rw [site2_eq] at h hb
      have : (m : ℤ) = (n : ℤ) := by omega
      exact_mod_cast this
  · intro n
    change s(![(n : ℤ) + 1, (0:ℤ)], ![(n : ℤ) + 1 + 1, 0]) ∈ jkr_lineH.edgeSet
    refine (jkr_line_seg_mem ((n : ℤ) + 1)).mpr ?_
    have : (0:ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    omega





theorem jkr_lineH_not_finite : ¬ jkr_lineH.edgeSet.Finite :=
  jkr_lineH_edgeSet_infinite
















theorem jkr_status :
    ¬ jwn_KeepReconnectResidue ∧
    (¬ jkr_lineH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
      ¬ ((whb_faceRegion jkr_lineH).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1]) ∧
    jkr_lineH.edgeSet.Infinite ∧
    (jwn_KeepReconnectResidue → jkr_FiniteKeepReconnectResidue) :=
  ⟨jkr_keepReconnectResidue_false,
    ⟨jkr_pq_not_reachable, jkr_faces_not_reconnect⟩,
    jkr_lineH_edgeSet_infinite,
    jkr_finite_of_keepReconnect⟩

end Lattice

end StatMech

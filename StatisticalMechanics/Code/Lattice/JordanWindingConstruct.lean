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
import Code.Lattice.WindingColoring
import Code.Lattice.JordanBridgeCycle
import Code.Lattice.JordanKeepDual

open SimpleGraph Set

namespace StatMech

namespace Lattice










noncomputable def jwn_cutCount (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  wcl_flipCount (wcl_cutFlip H f0 g0) w



theorem jwn_marked_iff (H : SimpleGraph (Site 2)) (f0 g0 a b : Site 2) :
    (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a) ↔ wcl_cutFlip H f0 g0 a b := by
  unfold wcl_cutFlip whc_isCross
  rw [Sym2.eq_swap]; tauto




theorem jwn_cutColoring_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (jwn_cutCount H f0 g0 w) ↔ (φ x ↔ φ y) := by
  classical
  unfold jwn_cutCount
  induction w with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [wcl_flipCount_cons]
    
    have hkey : wcl_cutFlip H f0 g0 a b ↔ (φ a ↔ ¬ φ b) := hcut a b hab
    have hmk : (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a) ↔
        wcl_cutFlip H f0 g0 a b := jwn_marked_iff H f0 g0 a b
    by_cases hm : (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a)
    · rw [if_pos hm, add_comm, Nat.even_add_one, ih]
      have := hkey.mp (hmk.mp hm)
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all
    · rw [if_neg hm, zero_add, ih]
      have hnm : ¬ wcl_cutFlip H f0 g0 a b := fun h => hm (Or.inl h)
      have := fun hh => hnm (hkey.mpr hh)
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all



theorem jwn_no_cutColoring_of_oddLoop (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) (hodd : ¬ Even (jwn_cutCount H f0 g0 w)) :
    ¬ ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ := by
  rintro ⟨φ, hcut⟩
  exact hodd ((jwn_cutColoring_closedEven H f0 g0 φ hcut w).mpr Iff.rfl)










noncomputable def jwn_squareLoop : (hypercubicLattice 2).Walk ![(0:ℤ), 0] ![(0:ℤ), 0] := by
  have a1 : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a2 : (hypercubicLattice 2).Adj ![(0:ℤ), -1] ![(1:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a3 : (hypercubicLattice 2).Adj ![(1:ℤ), -1] ![(1:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a4 : (hypercubicLattice 2).Adj ![(1:ℤ), 0] ![(0:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  exact .cons a1 (.cons a2 (.cons a3 (.cons a4 .nil)))


theorem jwn_cutFlip_bot_iff (a b : Site 2) :
    wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] a b ↔
      s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
  unfold wcl_cutFlip whc_isCross
  simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, false_or, or_false]


theorem jwn_squareLoop_cutCount :
    jwn_cutCount (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] jwn_squareLoop = 1 := by
  classical
  unfold jwn_cutCount
  set flip := wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] with hflip
  unfold jwn_squareLoop
  rw [wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons,
    wcl_flipCount_nil]
  rw [if_pos (Or.inl (by rw [hflip, jwn_cutFlip_bot_iff]))]
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, jwn_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, jwn_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, jwn_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]



theorem jwn_no_cutColoring_bot :
    ¬ ∃ φ : Site 2 → Prop,
      whc_CutColoring (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] φ := by
  refine jwn_no_cutColoring_of_oddLoop (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1]
    jwn_squareLoop ?_
  rw [jwn_squareLoop_cutCount]; decide






theorem jwn_bot_instance_valid :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true]
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num








theorem jwn_whitneyColoringResidue_false : ¬ whc_WhitneyColoringResidue := by
  intro hres
  obtain ⟨hpq, hnpq, hfg, hshared⟩ := jwn_bot_instance_valid
  obtain ⟨φ, hcut, _, _⟩ :=
    hres (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(1:ℤ), 0] ![(0:ℤ), 0] ![(0:ℤ), -1]
      hpq hnpq hfg hshared
  exact jwn_no_cutColoring_bot ⟨φ, hcut⟩














theorem jwn_bot_reconnect :
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] :=
  wcl_faceRegion_bot_reconnect














theorem jwn_cutColoring_of_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
    ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ :=
  ⟨wcl_windingColoring (wcl_cutFlip H f0 g0) f0,
    wcl_windingColoring_isCutColoring H f0 g0 hce f0⟩






theorem jwn_cutColoring_forces_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
  intro x w
  exact (jwn_cutColoring_closedEven H f0 g0 φ hcut w).mpr Iff.rfl















def jwn_KeepReconnectResidue : Prop :=
  ∀ (H : SimpleGraph (Site 2)) (p q f0 g0 : Site 2),
    (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
    (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) →
    ¬ H.Reachable p q →
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0




theorem jwn_keepReconnect_of_whitneyColoring (hres : whc_WhitneyColoringResidue) :
    jwn_KeepReconnectResidue := by
  intro H p q f0 g0 hpq hnpq hfg hshared hnr
  obtain ⟨φ, _hcut, htrack, hback⟩ := hres H p q f0 g0 hpq hnpq hfg hshared
  have hsame : (φ f0 ↔ φ g0) := by
    by_contra hdiff; exact hnr (htrack.mpr hdiff)
  exact hback hsame













theorem jwn_witness_square :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    ¬ (⊥ : SimpleGraph (Site 2)).Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  obtain ⟨hpq, hnpq, hfg, hshared⟩ := jwn_bot_instance_valid
  refine ⟨hpq, hnpq, hfg, hshared, ?_, jwn_bot_reconnect⟩
  intro h; rw [SimpleGraph.reachable_bot] at h
  simp only [site2_eq] at h; omega







theorem jwn_witness_ring :
    jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧
    s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉ (jei_pushGraph jkd_ringP ⊥).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧
    ¬ (jei_pushGraph jkd_ringP ⊥).Reachable (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hna : ¬ (⊥ : SimpleGraph jkd_ringP.V).Adj jkd_r0 jkd_r1 := by
    rw [SimpleGraph.bot_adj]; exact not_false
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] :=
    jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  have hnpq : s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉
      (jei_pushGraph jkd_ringP ⊥).edgeSet := jkd_wall_not_mem_pushGraph jkd_ringP ⊥ hna
  have hnr : ¬ (jei_pushGraph jkd_ringP ⊥).Reachable
      (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) := by
    rw [jei_push_reachable_iff]; intro h
    rw [SimpleGraph.reachable_bot] at h; exact jkd_r0_ne_r1 h
  exact ⟨jkd_ring_Gadj, hnpq, hfg, jkd_ring_shared_bottom, hnr, jkd_ring_witness_reach⟩
















theorem jwn_status :
    ¬ whc_WhitneyColoringResidue ∧
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    (whc_WhitneyColoringResidue → jwn_KeepReconnectResidue) :=
  ⟨jwn_whitneyColoringResidue_false, jwn_bot_reconnect, jwn_keepReconnect_of_whitneyColoring⟩

end Lattice

end StatMech

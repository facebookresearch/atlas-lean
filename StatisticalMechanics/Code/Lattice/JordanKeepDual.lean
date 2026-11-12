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
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.WhitneyBridge
import Code.Lattice.WhitneyCorrect
import Code.Lattice.JordanEulerInduction
import Code.Lattice.JordanFaithfulCount
import Code.Lattice.JordanWindingClose

open SimpleGraph Set

namespace StatMech

namespace Lattice











theorem jkd_wall_not_mem_pushGraph (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hnotK : ¬ K.Adj x y) :
    s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
  rintro ⟨u, v, hKuv, hu, hv⟩
  have hux : u = x := P.emb.injective hu
  have hvy : v = y := P.emb.injective hv
  subst hux; subst hvy
  exact hnotK hKuv


















theorem jkd_keepResidue_of_windingColoring (hres : whc_WhitneyColoringResidue)
    (P : PlanarZ2Subgraph) : jwc_KeepResidue P := by
  intro K hKle x y hadjG hnotK f0 g0 hfg hshared hnr
  
  have hpq : (hypercubicLattice 2).Adj (P.emb x) (P.emb y) := P.isSub hadjG
  have hnpq : s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet :=
    jkd_wall_not_mem_pushGraph P K hnotK
  obtain ⟨φ, hcut, htrack, hback⟩ :=
    hres (jei_pushGraph P K) (P.emb x) (P.emb y) f0 g0 hpq hnpq hfg hshared
  
  have hnrPush : ¬ (jei_pushGraph P K).Reachable (P.emb x) (P.emb y) := by
    rw [jei_push_reachable_iff]; exact hnr
  
  have hsame : (φ f0 ↔ φ g0) := by
    by_contra hdiff
    exact hnrPush (htrack.mpr hdiff)
  
  exact hback hsame















theorem jkd_faithfulDiscreteJordan_of_windingColoring (hres : whc_WhitneyColoringResidue)
    (P : PlanarZ2Subgraph) : whc_FaithfulDiscreteJordan P :=
  jwc_faithfulDiscreteJordan_of_keepResidue P (jkd_keepResidue_of_windingColoring hres P)




















theorem jkd_latadj {a b : Site 2} (h : (∑ i, (a i - b i).natAbs) = 1) :
    (hypercubicLattice 2).Adj a b := by rw [hypercubicLattice_adj]; exact h




theorem jkd_faceRegion_botPush_adj (P : PlanarZ2Subgraph) {a b : Site 2}
    (hlat : (hypercubicLattice 2).Adj a b) :
    (whb_faceRegion (jei_pushGraph P ⊥)).Adj a b := by
  rw [whb_faceRegion_adj, jei_pushGraph_bot]
  refine ⟨hlat, ?_⟩
  rw [SimpleGraph.edgeSet_bot]
  exact fun h => h



theorem jkd_shared_bottom :
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) := by
  rw [jbc_Pce_emb0, jbc_Pce_emb1,
    show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
  unfold faceCorner00 faceCorner10; norm_num







theorem jkd_witness_square_reach :
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  set wall := s(![(0:ℤ), 0], ![(0:ℤ), -1]) with hwall
  
  have mkAdj : ∀ a b : Site 2, (hypercubicLattice 2).Adj a b → s(a, b) ≠ wall →
      ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {wall}).Adj a b := by
    intro a b hlat hne
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨jkd_faceRegion_botPush_adj jbc_Pce hlat, hne⟩
  have e1 : ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {wall}).Adj
      ![(0:ℤ), 0] ![(1:ℤ), 0] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e2 : ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {wall}).Adj
      ![(1:ℤ), 0] ![(1:ℤ), -1] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e3 : ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {wall}).Adj
      ![(1:ℤ), -1] ![(0:ℤ), -1] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  exact e1.reachable.trans (e2.reachable.trans e3.reachable)












theorem jkd_keepResidue_witness_square :
    
    (⊥ : SimpleGraph jbc_Pce.V) ≤ jbc_Pce.G ∧
    
    jbc_Pce.G.Adj jbc_v0 jbc_v1 ∧
    
    ¬ (⊥ : SimpleGraph jbc_Pce.V).Adj jbc_v0 jbc_v1 ∧
    
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∧
    
    ¬ (⊥ : SimpleGraph jbc_Pce.V).Reachable jbc_v0 jbc_v1 ∧
    
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  refine ⟨bot_le, jbc_Pce_Gadj, ?_, ?_, jkd_shared_bottom, ?_, jkd_witness_square_reach⟩
  · rw [SimpleGraph.bot_adj]; exact not_false
  · exact jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  · 
    intro h
    rw [SimpleGraph.reachable_bot] at h
    exact jbc_v0_ne_v1 h






theorem jkd_keepResidue_witness_consistent (hres : whc_WhitneyColoringResidue) :
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hkeep := jkd_keepResidue_of_windingColoring hres jbc_Pce
  have hna : ¬ (⊥ : SimpleGraph jbc_Pce.V).Adj jbc_v0 jbc_v1 := by
    rw [SimpleGraph.bot_adj]; exact not_false
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    exact jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  have hnr : ¬ (⊥ : SimpleGraph jbc_Pce.V).Reachable jbc_v0 jbc_v1 := by
    intro h; rw [SimpleGraph.reachable_bot] at h; exact jbc_v0_ne_v1 h
  exact hkeep ⊥ bot_le jbc_Pce_Gadj hna hfg jkd_shared_bottom hnr











def jkd_gr9emb (i : Fin 9) : Site 2 :=
  match i with
  | 0 => ![0, 0] | 1 => ![1, 0] | 2 => ![2, 0]
  | 3 => ![0, 1] | 4 => ![1, 1] | 5 => ![2, 1]
  | 6 => ![0, 2] | 7 => ![1, 2] | 8 => ![2, 2]

theorem jkd_gr9emb_inj : Function.Injective jkd_gr9emb := by decide +kernel


def jkd_gr9rel (i j : Fin 9) : Bool :=
  let ci := (i : ℕ) % 3; let ri := (i : ℕ) / 3
  let cj := (j : ℕ) % 3; let rj := (j : ℕ) / 3
  (ci == cj && (ri == rj + 1 || rj == ri + 1)) || (ri == rj && (ci == cj + 1 || cj == ci + 1))


def jkd_gr9G : SimpleGraph (Fin 9) where
  Adj i j := jkd_gr9rel i j
  symm := by intro i j h; revert h; revert i j; decide
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

@[simp] theorem jkd_gr9G_adj (i j : Fin 9) : jkd_gr9G.Adj i j ↔ jkd_gr9rel i j := Iff.rfl

theorem jkd_gr9_isSub : ∀ ⦃i j : Fin 9⦄, jkd_gr9G.Adj i j →
    (hypercubicLattice 2).Adj (jkd_gr9emb i) (jkd_gr9emb j) := by
  intro i j h; rw [jkd_gr9G_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jkd_gr9rel, jkd_gr9emb]


noncomputable def jkd_ringP : PlanarZ2Subgraph where
  V := Fin 9
  finV := inferInstance
  decV := inferInstance
  G := jkd_gr9G
  emb := ⟨jkd_gr9emb, jkd_gr9emb_inj⟩
  isSub := jkd_gr9_isSub


def jkd_r0 : Fin 9 := 0

def jkd_r1 : Fin 9 := 1

theorem jkd_r0_ne_r1 : jkd_r0 ≠ jkd_r1 := by decide



theorem jkd_ring_centre_deg4 : jkd_gr9G.neighborSet 4 = {1, 3, 5, 7} := by
  ext j; rw [SimpleGraph.mem_neighborSet, jkd_gr9G_adj]; fin_cases j <;> simp [jkd_gr9rel]


theorem jkd_ring_Gadj : jkd_ringP.G.Adj jkd_r0 jkd_r1 := by
  change jkd_gr9G.Adj jkd_r0 jkd_r1; rw [jkd_gr9G_adj]; decide

theorem jkd_ring_emb0 : jkd_ringP.emb jkd_r0 = ![0, 0] := rfl
theorem jkd_ring_emb1 : jkd_ringP.emb jkd_r1 = ![1, 0] := rfl


theorem jkd_ring_shared_bottom :
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) := by
  rw [jkd_ring_emb0, jkd_ring_emb1,
    show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
  unfold faceCorner00 faceCorner10; norm_num




theorem jkd_ring_witness_reach :
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  set wall := s(![(0:ℤ), 0], ![(0:ℤ), -1]) with hwall
  have mkAdj : ∀ a b : Site 2, (hypercubicLattice 2).Adj a b → s(a, b) ≠ wall →
      ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {wall}).Adj a b := by
    intro a b hlat hne
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨jkd_faceRegion_botPush_adj jkd_ringP hlat, hne⟩
  have e1 : ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {wall}).Adj
      ![(0:ℤ), 0] ![(1:ℤ), 0] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e2 : ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {wall}).Adj
      ![(1:ℤ), 0] ![(1:ℤ), -1] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e3 : ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {wall}).Adj
      ![(1:ℤ), -1] ![(0:ℤ), -1] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  exact e1.reachable.trans (e2.reachable.trans e3.reachable)








theorem jkd_keepResidue_witness_ring :
    (⊥ : SimpleGraph jkd_ringP.V) ≤ jkd_ringP.G ∧
    jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧
    ¬ (⊥ : SimpleGraph jkd_ringP.V).Adj jkd_r0 jkd_r1 ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧
    ¬ (⊥ : SimpleGraph jkd_ringP.V).Reachable jkd_r0 jkd_r1 ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  refine ⟨bot_le, jkd_ring_Gadj, ?_, ?_, jkd_ring_shared_bottom, ?_, jkd_ring_witness_reach⟩
  · rw [SimpleGraph.bot_adj]; exact not_false
  · exact jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  · intro h; rw [SimpleGraph.reachable_bot] at h; exact jkd_r0_ne_r1 h




theorem jkd_keepResidue_witness_ring_consistent (hres : whc_WhitneyColoringResidue) :
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hkeep := jkd_keepResidue_of_windingColoring hres jkd_ringP
  have hna : ¬ (⊥ : SimpleGraph jkd_ringP.V).Adj jkd_r0 jkd_r1 := by
    rw [SimpleGraph.bot_adj]; exact not_false
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] :=
    jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  have hnr : ¬ (⊥ : SimpleGraph jkd_ringP.V).Reachable jkd_r0 jkd_r1 := by
    intro h; rw [SimpleGraph.reachable_bot] at h; exact jkd_r0_ne_r1 h
  exact hkeep ⊥ bot_le jkd_ring_Gadj hna hfg jkd_ring_shared_bottom hnr

end Lattice

end StatMech

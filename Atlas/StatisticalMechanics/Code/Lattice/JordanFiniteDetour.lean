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
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.JordanEulerInduction
import Code.Lattice.WhitneyBridge
import Code.Lattice.WhitneyCorrect
import Code.Lattice.JordanKeepReconnect
import Code.Lattice.JordanWindingConstruct

open SimpleGraph Set

namespace StatMech

namespace Lattice












theorem jfd_shared_exterior (R : ℕ) {a b : Site 2}
    (ha : a ∈ exterior 2 (R + 1)) (hab : (hypercubicLattice 2).Adj a b) :
    ∀ x ∈ sharedPrimalEdge a b, x ∈ exterior 2 R := by
  classical
  obtain ⟨i, hi⟩ := ha
  have hadj := hab
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  
  have hcoord : (R : ℤ) + 1 < a 0 ∨ a 0 < -((R : ℤ) + 1) ∨
      (R : ℤ) + 1 < a 1 ∨ a 1 < -((R : ℤ) + 1) := by
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · rcases Int.natAbs_eq (a 0) with h | h <;> omega
    · rcases Int.natAbs_eq (a 1) with h | h <;> omega
  
  have ha' : a = ![a 0, a 1] := by funext j; fin_cases j <;> rfl
  have hb' : b = ![b 0, b 1] := by funext j; fin_cases j <;> rfl
  
  intro x hx
  rw [mem_exterior]
  
  have hExt0 : ∀ c d : ℤ, (R : ℤ) + 1 ≤ c ∨ c ≤ -((R : ℤ) + 1) →
      (∃ j, R < ((![c, d] : Site 2) j).natAbs) := by
    intro c d hz
    refine ⟨0, ?_⟩
    have : ((![c, d] : Site 2) 0) = c := by simp
    rw [this]; rcases Int.natAbs_eq c with h | h <;> omega
  have hExt1 : ∀ c d : ℤ, (R : ℤ) + 1 ≤ d ∨ d ≤ -((R : ℤ) + 1) →
      (∃ j, R < ((![c, d] : Site 2) j).natAbs) := by
    intro c d hz
    refine ⟨1, ?_⟩
    have : ((![c, d] : Site 2) 1) = d := by simp
    rw [this]; rcases Int.natAbs_eq d with h | h <;> omega
  by_cases h0 : a 0 = b 0
  · 
    rw [ha', hb', h0, whc_shared_hstep, Sym2.mem_iff] at hx
    rcases hcoord with hb | hb | hb | hb
    · rcases hx with rfl | rfl <;> exact hExt0 _ _ (by omega)
    · rcases hx with rfl | rfl <;> exact hExt0 _ _ (by omega)
    · rcases hx with rfl | rfl <;>
        exact hExt1 _ _ (by
          have := max_choice (a 1) (b 1); rcases this with h | h <;> rw [h] <;> omega)
    · rcases hx with rfl | rfl <;>
        exact hExt1 _ _ (by
          have := max_choice (a 1) (b 1); rcases this with h | h <;> rw [h] <;> omega)
  · have h1 : a 1 = b 1 := by omega
    
    rw [ha', hb', h1, whc_shared_vstep (a 0) (b 0) (b 1) h0, Sym2.mem_iff] at hx
    rcases hcoord with hb | hb | hb | hb
    · rcases hx with rfl | rfl <;>
        exact hExt0 _ _ (by
          have := max_choice (a 0) (b 0); rcases this with h | h <;> rw [h] <;> omega)
    · rcases hx with rfl | rfl <;>
        exact hExt0 _ _ (by
          have := max_choice (a 0) (b 0); rcases this with h | h <;> rw [h] <;> omega)
    · rcases hx with rfl | rfl <;> exact hExt1 _ _ (by omega)
    · rcases hx with rfl | rfl <;> exact hExt1 _ _ (by omega)















theorem jfd_not_edge_of_not_support (H : SimpleGraph (Site 2)) {u v : Site 2}
    (hu : u ∉ H.support) : s(u, v) ∉ H.edgeSet := by
  intro hmem
  rw [SimpleGraph.mem_edgeSet] at hmem
  exact hu ⟨v, hmem⟩




theorem jfd_deleted_adj_of_exterior (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R)
    {a b : Site 2} (ha : a ∈ exterior 2 (R + 1)) (_hb : b ∈ exterior 2 (R + 1))
    (hab : (hypercubicLattice 2).Adj a b) :
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Adj a b := by
  rw [deleteEdges_adj, Set.mem_singleton_iff, whb_faceRegion_adj]
  refine ⟨⟨hab, ?_⟩, ?_⟩
  · 
    obtain ⟨p, q, hpq, hpqadj⟩ := sharedPrimalEdge_isLatticeEdge hab
    rw [hpq]
    have hp : p ∈ exterior 2 R := by
      have := jfd_shared_exterior R ha hab
      rw [hpq] at this; exact this p (Sym2.mem_mk_left p q)
    have hpns : p ∉ H.support := by
      intro hsupp
      have := hHR p hsupp
      rw [exterior_eq_compl_box] at hp; exact hp this
    exact jfd_not_edge_of_not_support H hpns
  · 
    intro heq
    rw [Sym2.eq_iff] at heq
    
    have hane : ∀ z : Site 2, z ∈ box 2 R → a ≠ z := by
      intro z hz hcon
      obtain ⟨i, hi⟩ := ha
      have := hz i
      rw [hcon] at hi
      omega
    rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hane f0 hf0 h1
    · exact hane g0 hg0 h1





noncomputable def jfd_extToDeletedHom (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R) :
    (hypercubicLattice 2).induce (exterior 2 (R + 1)) →g
      (whb_faceRegion H).deleteEdges {s(f0, g0)} where
  toFun v := (v : Site 2)
  map_rel' := by
    intro a b hab
    exact jfd_deleted_adj_of_exterior H R f0 g0 hHR hf0 hg0 a.2 b.2 hab





theorem jfd_exterior_reachable_deleted (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 (R + 1)) (hy : y ∈ exterior 2 (R + 1)) :
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable x y := by
  have hmap := (box_exterior_connected (R + 1) (by norm_num) x y hx hy).map
    (jfd_extToDeletedHom H R f0 g0 hHR hf0 hg0)
  simpa [jfd_extToDeletedHom] using hmap
























theorem jfd_reconnect_of_both_escape (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R)
    {ef eg : Site 2} (hef : ef ∈ exterior 2 (R + 1)) (heg : eg ∈ exterior 2 (R + 1))
    (hfef : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef)
    (hgeg : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg) :
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  hfef.trans ((jfd_exterior_reachable_deleted H R f0 g0 hHR hf0 hg0 hef heg).trans hgeg.symm)









def jfd_SameComponentResidue : Prop := jkr_FiniteKeepReconnectResidue








theorem jfd_reconnect_split (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R)
    (hcase : (∃ ef ∈ exterior 2 (R + 1),
        ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef) ∧
        (∃ eg ∈ exterior 2 (R + 1),
        ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg)) :
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  obtain ⟨⟨ef, hef, hfef⟩, ⟨eg, heg, hgeg⟩⟩ := hcase
  exact jfd_reconnect_of_both_escape H R f0 g0 hHR hf0 hg0 hef heg hfef hgeg




theorem jfd_sameComponent_iff_finiteKeep :
    jfd_SameComponentResidue ↔ jkr_FiniteKeepReconnectResidue := Iff.rfl



















theorem jfd_witnesses :
    
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    
    jkr_lineH.edgeSet.Infinite := by
  refine ⟨?_, ?_, ?_, jkr_lineH_edgeSet_infinite⟩
  · exact (jkr_witness_bot).2.2.2.2.2
  · exact (jkr_witness_square).2.2.2.2.2
  · exact (jkr_witness_ring).2.2.2.2.2





















theorem jfd_status :
    
    (∀ (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2),
      (∀ v ∈ H.support, v ∈ box 2 R) → f0 ∈ box 2 R → g0 ∈ box 2 R →
      ∀ {ef eg : Site 2}, ef ∈ exterior 2 (R + 1) → eg ∈ exterior 2 (R + 1) →
      ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef →
      ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg →
      ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) ∧
    
    (jfd_SameComponentResidue ↔ jkr_FiniteKeepReconnectResidue) ∧
    
    (jwn_KeepReconnectResidue → jkr_FiniteKeepReconnectResidue) :=
  ⟨fun H R f0 g0 hHR hf0 hg0 {_ef _eg} hef heg hfef hgeg =>
      jfd_reconnect_of_both_escape H R f0 g0 hHR hf0 hg0 hef heg hfef hgeg,
    jfd_sameComponent_iff_finiteKeep,
    jkr_finite_of_keepReconnect⟩

end Lattice

end StatMech

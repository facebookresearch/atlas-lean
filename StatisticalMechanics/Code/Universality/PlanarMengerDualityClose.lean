/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































































import Mathlib
import Code.RSW.Defs
import Code.RSW.SelfDuality
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarDual
import Code.Lattice.JordanEnclosure
import Code.Universality.JordanExhaustivityClose
import Code.Universality.FaceDualDichotomy
import Code.Universality.FrameChangeIso
import Code.Universality.BoxCrossingDichotomy
import Code.Universality.BoxCrossingDichotomyClose
import Code.Universality.RSWDualVCrossingClose

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality












theorem pmd_faceVAdj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ)
    (hcl : ω s(![a, b + 1], ![a + 1, b + 1]) = false) :
    (fci_faceOpenDual ω).Adj ![a, b] ![a, b + 1] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ?_⟩
  rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11; exact hcl





theorem pmd_faceHAdj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ)
    (hcl : ω s(![a + 1, b], ![a + 1, b + 1]) = false) :
    (fci_faceOpenDual ω).Adj ![a, b] ![a + 1, b] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ?_⟩
  rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11; exact hcl

















def pmd_FaceDualVCrossing (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (a₀ a₁ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ n - 1 ∧
    (fci_faceOpenDual ω).Reachable ![a₀, -1] ![a₁, n]








theorem pmd_faceDualVCrossing_of_spanningContour (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {u : Site 2} (c : (fci_faceOpenDual ω).Walk u u)
    {a₀ a₁ : ℤ} (ha0 : 0 ≤ a₀) (ha0' : a₀ ≤ n - 1) (ha1 : 0 ≤ a₁) (ha1' : a₁ ≤ n - 1)
    (hbot : (![a₀, -1] : Site 2) ∈ c.support) (htop : (![a₁, n] : Site 2) ∈ c.support) :
    pmd_FaceDualVCrossing ω n := by
  classical
  refine ⟨a₀, a₁, ha0, ha0', ha1, ha1', ?_⟩
  exact (Reachable.symm ⟨c.takeUntil _ hbot⟩).trans ⟨c.takeUntil _ htop⟩





theorem pmd_faceDualV_implies_spanningReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pmd_FaceDualVCrossing ω n) :
    ∃ (a₀ a₁ : ℤ), (fci_faceOpenDual ω).Reachable ![a₀, -1] ![a₁, n] := by
  obtain ⟨a₀, a₁, _, _, _, _, hreach⟩ := h
  exact ⟨a₀, a₁, hreach⟩































def pmd_boxFaceBarrier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧
    ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧
      bdEdge (bcd_leftReach ω n) s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n
  symm := by
    rintro f g ⟨hadj, p, q, hpq, hbd, hp, hq⟩
    refine ⟨hadj.symm, q, p, ?_, ?_, hq, hp⟩
    · rw [← sharedPrimalEdge_comm_of_adj hadj, hpq, Sym2.eq_swap]
    · rwa [Sym2.eq_swap]
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem pmd_boxFaceBarrier_adj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (f g : Site 2) :
    (pmd_boxFaceBarrier ω n).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧
        ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧
          bdEdge (bcd_leftReach ω n) s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n := Iff.rfl








theorem pmd_boxFaceBarrier_le_faceOpenDual (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pmd_boxFaceBarrier ω n ≤ fci_faceOpenDual ω := by
  rintro f g ⟨hadj, p, q, hpq, hbd, hp, hq⟩
  refine ⟨hadj, ?_⟩
  have hpadj : (hypercubicLattice 2).Adj p q := by
    obtain ⟨p', q', hpq', hadj'⟩ := sharedPrimalEdge_isLatticeEdge hadj
    rw [hpq'] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · exact hadj'
    · exact hadj'.symm
  rw [bdEdge_mk] at hbd
  rw [hpq]
  by_cases hpL : p ∈ bcd_leftReach ω n
  · exact bcd_leftReach_boundary_closed ω n hpL hq hpadj (hbd.mp hpL)
  · have hqL : q ∈ bcd_leftReach ω n := by by_contra hqn; exact hpL (hbd.mpr hqn)
    rw [Sym2.eq_swap]
    exact bcd_leftReach_boundary_closed ω n hqL hp hpadj.symm hpL









def pmd_BarrierConnectsRows (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (a₀ a₁ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ n - 1 ∧
    (pmd_boxFaceBarrier ω n).Reachable ![a₀, -1] ![a₁, n]









theorem pmd_faceDualVCrossing_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pmd_BarrierConnectsRows ω n) : pmd_FaceDualVCrossing ω n := by
  obtain ⟨a₀, a₁, ha0, ha0', ha1, ha1', hreach⟩ := h
  exact ⟨a₀, a₁, ha0, ha0', ha1, ha1', hreach.mono (pmd_boxFaceBarrier_le_faceOpenDual ω n)⟩







theorem pmd_contour_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle :=
  fdd_leftReach_dualCircuit ω n hn hnoH






theorem pmd_exhaustivity_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (h : pmd_BarrierConnectsRows ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (pmd_faceDualVCrossing_of_residue ω n h)













theorem pmd_wall_faceVAdj {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    (fci_faceOpenDual bcc_wallCfg).Adj ![0, b] ![0, b + 1] := by
  apply pmd_faceVAdj_of_closed
  simp only [bcc_wallCfg]
  rcases hb with rfl | rfl | rfl <;> decide










theorem pmd_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 := by
  refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 := (pmd_wall_faceVAdj (b := -1) (by tauto)).reachable
  have h2 := (pmd_wall_faceVAdj (b := 0) (by tauto)).reachable
  have h3 := (pmd_wall_faceVAdj (b := 1) (by tauto)).reachable
  norm_num at h1 h2 h3 ⊢
  exact (h1.trans h2).trans h3







theorem pmd_wall_barrierVAdj {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, b] ![0, b + 1] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![0, b + 1], ![1, b + 1],
    ?_, ?_, ?_, ?_⟩
  · rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11; rfl
  · rw [bdEdge_mk]
    constructor
    · intro _
      exact fun hc => by
        have := rdv_leftReach_wall_x0 hc; simp at this
    · intro hno
      exact jex_leftSide_subset_leftReach bcc_wallCfg 2
        ⟨by rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp, by simp⟩
  · rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp
  · rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp








theorem pmd_wall_barrierConnectsRows : pmd_BarrierConnectsRows bcc_wallCfg 2 := by
  refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 := (pmd_wall_barrierVAdj (b := -1) (by tauto)).reachable
  have h2 := (pmd_wall_barrierVAdj (b := 0) (by tauto)).reachable
  have h3 := (pmd_wall_barrierVAdj (b := 1) (by tauto)).reachable
  norm_num at h1 h2 h3 ⊢
  exact (h1.trans h2).trans h3





theorem pmd_wall_faceDualV_via_residue : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  pmd_faceDualVCrossing_of_residue bcc_wallCfg 2 pmd_wall_barrierConnectsRows




theorem pmd_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall




theorem pmd_wall_noH_yet_faceDualV :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, pmd_wall_faceDualVCrossing⟩







theorem pmd_wall_only_face_frame_works :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧
      ¬ jex_DualBarrierVCrossing bcc_wallCfg 2 ∧
      ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 ∧
      pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, bcc_noV_wall, rdv_rotResidue_false_on_noH, pmd_wall_faceDualVCrossing⟩

end Universality

end StatMech

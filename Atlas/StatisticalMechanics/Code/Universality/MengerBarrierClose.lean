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
import Code.Universality.PlanarMengerDualityClose

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality








def mbc_IsRightFrontier (ω : ConfigSpace (Sym2 (Site 2))) (n c r : ℤ) : Prop :=
  0 ≤ c ∧ c ≤ n - 1 ∧ (![c, r] : Site 2) ∈ bcd_leftReach ω n ∧
    ∀ c' : ℤ, c < c' → c' ≤ n → (![c', r] : Site 2) ∉ bcd_leftReach ω n



theorem mbc_rightFrontier_succ_notMem (ω : ConfigSpace (Sym2 (Site 2))) (n c r : ℤ)
    (h : mbc_IsRightFrontier ω n c r) : (![c + 1, r] : Site 2) ∉ bcd_leftReach ω n := by
  obtain ⟨hc0, hcn, _hcL, hmax⟩ := h
  exact hmax (c + 1) (by omega) (by omega)






theorem mbc_exists_rightFrontier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {r : ℤ} (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    ∃ c : ℤ, mbc_IsRightFrontier ω n c r := by
  classical
  have h0L : (![0, r] : Site 2) ∈ bcd_leftReach ω n := by
    apply jex_leftSide_subset_leftReach
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp, by simp [hn], by simpa using hr0, by simpa using hrn⟩
  have hnL : (![n, r] : Site 2) ∉ bcd_leftReach ω n := by
    apply jex_rightSide_notin_leftReach ω n hnoH
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  let S : Finset ℤ := (Finset.Icc 0 n).filter (fun c => (![c, r] : Site 2) ∈ bcd_leftReach ω n)
  have h0mem : (0 : ℤ) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨le_refl 0, hn⟩, h0L⟩
  obtain ⟨c, hcS, hcmax⟩ := S.exists_max_image id ⟨0, h0mem⟩
  simp only [S, Finset.mem_filter, Finset.mem_Icc] at hcS
  obtain ⟨⟨hc0, hcn⟩, hcL⟩ := hcS
  have hcltn : c < n := by
    rcases lt_or_eq_of_le hcn with h | h
    · exact h
    · subst h; exact absurd hcL hnL
  refine ⟨c, hc0, by omega, hcL, ?_⟩
  intro c' hcc' hc'n hc'L
  have hmem : c' ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hc'n⟩, hc'L⟩
  have := hcmax c' hmem; simp only [id] at this; omega











theorem mbc_rung_vAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    (pmd_boxFaceBarrier ω n).Adj ![c, r - 1] ![c, r] := by
  obtain ⟨hc0, hcn, hcL, _hmax⟩ := htr
  have hc1 : (![c + 1, r] : Site 2) ∉ bcd_leftReach ω n :=
    mbc_rightFrontier_succ_notMem ω n c r ⟨hc0, hcn, hcL, _hmax⟩
  have hface : (![c, r] : Site 2) = ![c, (r - 1) + 1] := by funext i; fin_cases i <;> simp
  rw [pmd_boxFaceBarrier_adj]
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![c, r], ![c + 1, r], ?_, ?_, ?_, ?_⟩
  · rw [hface, sharedPrimalEdge_top]
    unfold faceCorner01 faceCorner11
    have hrr : (r - 1) + 1 = r := by ring
    rw [hrr]
  · rw [bdEdge_mk]; exact ⟨fun _ hcontra => hc1 hcontra, fun _ => hcL⟩
  · rw [mem_rect]
    exact ⟨by simpa using hc0, by simp; omega, by simpa using hr0, by simpa using hrn⟩
  · rw [mem_rect]
    exact ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩













def mbc_FrontierRungsConnect (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (r : ℤ), 0 ≤ r → r ≤ n - 1 → ∀ (c c' : ℤ),
    mbc_IsRightFrontier ω n c r → mbc_IsRightFrontier ω n c' (r + 1) →
      (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c', r]





theorem mbc_reach_to_row (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : mbc_FrontierRungsConnect ω n)
    {c0 : ℤ} (h0 : mbc_IsRightFrontier ω n c0 0) :
    ∀ (k : ℕ), (k : ℤ) ≤ n →
      ∃ ck : ℤ, mbc_IsRightFrontier ω n ck (k : ℤ) ∧
        (pmd_boxFaceBarrier ω n).Reachable ![c0, -1] ![ck, (k : ℤ)] := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨c0, h0, ?_⟩
    have hrung : (pmd_boxFaceBarrier ω n).Adj ![c0, (0 : ℤ) - 1] ![c0, (0 : ℤ)] :=
      mbc_rung_vAdj ω n (le_refl 0) hn h0
    simpa using hrung.reachable
  | succ m ih =>
    intro hk
    have hm : (m : ℤ) ≤ n := by push_cast at hk ⊢; omega
    obtain ⟨cm, hcm, hreachm⟩ := ih hm
    have hm1_0 : (0 : ℤ) ≤ ((m : ℤ) + 1) := by positivity
    have hm1_n : ((m : ℤ) + 1) ≤ n := by push_cast at hk; omega
    obtain ⟨cm1, hcm1⟩ := mbc_exists_rightFrontier ω n hn hnoH hm1_0 hm1_n
    have hconn : (pmd_boxFaceBarrier ω n).Reachable ![cm, (m : ℤ)] ![cm1, (m : ℤ)] := by
      have hmle : (m : ℤ) ≤ n - 1 := by omega
      exact hres (m : ℤ) (by positivity) hmle cm cm1 hcm hcm1
    have hrung : (pmd_boxFaceBarrier ω n).Adj ![cm1, ((m : ℤ) + 1) - 1] ![cm1, ((m : ℤ) + 1)] :=
      mbc_rung_vAdj ω n hm1_0 hm1_n hcm1
    have hrung' : (pmd_boxFaceBarrier ω n).Adj ![cm1, (m : ℤ)] ![cm1, ((m : ℤ) + 1)] := by
      have he : ((m : ℤ) + 1) - 1 = (m : ℤ) := by ring
      rwa [he] at hrung
    refine ⟨cm1, ?_, ?_⟩
    · have hc : (((m : ℕ) + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hc]; exact hcm1
    · have hstep : (pmd_boxFaceBarrier ω n).Reachable ![cm, (m : ℤ)] ![cm1, ((m : ℤ) + 1)] :=
        hconn.trans hrung'.reachable
      have hcast : (((m : ℕ) + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast]; exact hreachm.trans hstep







theorem mbc_barrierConnectsRows_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hres : mbc_FrontierRungsConnect ω n) :
    pmd_BarrierConnectsRows ω n := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨c0, hc0⟩ := mbc_exists_rightFrontier ω (m : ℤ) hn hnoH (le_refl 0) (by positivity)
  obtain ⟨cn, hcn, hreach⟩ := mbc_reach_to_row ω (m : ℤ) hn hnoH hres hc0 m (le_refl _)
  exact ⟨c0, cn, hc0.1, hc0.2.1, hcn.1, hcn.2.1, hreach⟩






theorem mbc_faceDualVCrossing_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hres : mbc_FrontierRungsConnect ω n) :
    pmd_FaceDualVCrossing ω n :=
  pmd_faceDualVCrossing_of_residue ω n (mbc_barrierConnectsRows_of_residue ω n hn hnoH hres)




theorem mbc_exhaustivity_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hres : mbc_FrontierRungsConnect ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (mbc_faceDualVCrossing_of_residue ω n hn hnoH hres)






theorem mbc_wall_rightFrontier_zero {c r : ℤ} (h : mbc_IsRightFrontier bcc_wallCfg 2 c r) :
    c = 0 := by
  obtain ⟨_hc0, _hcn, hcL, _hmax⟩ := h
  simpa using rdv_leftReach_wall_x0 hcL






theorem mbc_wall_frontierRungsConnect : mbc_FrontierRungsConnect bcc_wallCfg 2 := by
  intro r _hr0 _hrn c c' hc hc'
  have e1 : c = 0 := mbc_wall_rightFrontier_zero hc
  have e2 : c' = 0 := mbc_wall_rightFrontier_zero hc'
  subst e1; subst e2
  exact Reachable.refl _






theorem mbc_wall_barrierConnectsRows : pmd_BarrierConnectsRows bcc_wallCfg 2 :=
  mbc_barrierConnectsRows_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    mbc_wall_frontierRungsConnect





theorem mbc_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  mbc_faceDualVCrossing_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    mbc_wall_frontierRungsConnect







theorem mbc_residue_atom_single_step (ω : ConfigSpace (Sym2 (Site 2))) (n r c c' : ℤ)
    (h : c = c') : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c', r] := by
  subst h; exact Reachable.refl _





theorem mbc_wall_rightFrontier_at {r : ℤ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    mbc_IsRightFrontier bcc_wallCfg 2 0 r := by
  refine ⟨le_refl 0, by norm_num, ?_, ?_⟩
  · apply jex_leftSide_subset_leftReach
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp, by norm_num, by simpa using hr0, by simpa using hr2⟩
  · intro c' _hc' hc'2 hc'L
    have := rdv_leftReach_wall_x0 hc'L
    simp at this; omega








theorem mbc_wall_bottom_rung_real :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ) - 1] ![0, (0 : ℤ)] :=
  mbc_rung_vAdj bcc_wallCfg 2 (le_refl 0) (by norm_num)
    (mbc_wall_rightFrontier_at (le_refl 0) (by norm_num))



theorem mbc_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall

end Universality

end StatMech

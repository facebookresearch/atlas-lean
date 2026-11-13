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
import Code.Lattice.SegmentConn
import Code.Universality.JordanExhaustivityClose
import Code.Universality.PlanarMengerDualityClose
import Code.Universality.MengerBarrierClose
import Code.Universality.CoastlineContinuityClose
import Code.Universality.CoastlineAnchorClose
import Code.Universality.CircuitReachClose
import Code.Universality.BoxArcConnectsClose

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality







theorem rcm_horizEdge_faces_pmdAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
    (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x, y - 1] := by
  rw [pmd_boxFaceBarrier_adj]
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![x, y], ![x + 1, y], ?_, hbd, hp, hq⟩
  rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; rfl





theorem rcm_vertEdge_faces_pmdAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x, y + 1]))
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x, y + 1] : Site 2) ∈ rect 0 n 0 n) :
    (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x - 1, y] := by
  rw [pmd_boxFaceBarrier_adj]
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![x, y], ![x, y + 1], ?_, hbd, hp, hq⟩
  rw [sharedPrimalEdge_left]; unfold faceCorner00 faceCorner01; rfl




theorem rcm_LR_edge_bdEdge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (hpL : p ∈ bcd_leftReach ω n) (hqR : q ∈ bac_rightComplement ω n) :
    bdEdge (bcd_leftReach ω n) s(p, q) := by
  rw [bdEdge_mk]
  have hqnotL : q ∉ bcd_leftReach ω n := (bac_rightComplement_mem ω n hqR).2
  exact ⟨fun _ => hqnotL, fun _ => hpL⟩





theorem rcm_LR_horizEdge_faces_pmdAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hpL : (![x, y] : Site 2) ∈ bcd_leftReach ω n)
    (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
    (pmd_boxFaceBarrier ω n).Adj ![x, y] ![x, y - 1] :=
  rcm_horizEdge_faces_pmdAdj ω n (rcm_LR_edge_bdEdge ω n hpL hqR) hp hq








theorem rcm_rightWall_reaches_in_boxMinusL (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {t : ℤ} (ht0 : 0 ≤ t) (htn : t ≤ n) :
    ∃ (h0 : (![n, 0] : Site 2) ∈ bac_boxMinusL ω n)
      (ht : (![n, t] : Site 2) ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨![n, 0], h0⟩ ⟨![n, t], ht⟩ := by
  have hn : 0 ≤ n := le_trans ht0 htn
  
  have hmem : ∀ s : ℤ, 0 ≤ s → s ≤ n → (![n, s] : Site 2) ∈ bac_boxMinusL ω n := by
    intro s hs0 hsn
    have hR : (![n, s] : Site 2) ∈ rightSide 0 n 0 n := by
      refine ⟨?_, by simp⟩
      rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hs0, by simpa using hsn⟩
    exact ⟨rightSide_subset hR, jex_rightSide_notin_leftReach ω n hnoH hR⟩
  
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ht0
  have hseg : ∀ k : ℕ, k ≤ m →
      Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + (k : ℤ))
        ∈ bac_boxMinusL ω n := by
    intro k hk
    have hval : Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + (k : ℤ))
        = ![n, (k : ℤ)] := by funext i; fin_cases i <;> simp [Function.update]
    rw [hval]
    have hk' : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hk
    exact hmem (k : ℤ) (by positivity) (by omega)
  have hreach := segment_connectedWithin (d := 2) (bac_boxMinusL ω n) (1 : Fin 2)
    (![n, 0] : Site 2) m hseg
  have e0 : Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + ((0 : ℕ) : ℤ))
      = ![n, 0] := by funext i; fin_cases i <;> simp [Function.update]
  have em : Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + (m : ℤ))
      = ![n, t] := by
    funext i; fin_cases i
    · simp [Function.update]
    · simp only [Function.update]; simp; omega
  have h0 : (![n, 0] : Site 2) ∈ bac_boxMinusL ω n := hmem 0 le_rfl hn
  have ht : (![n, t] : Site 2) ∈ bac_boxMinusL ω n := hmem t ht0 htn
  refine ⟨h0, ht, ?_⟩
  have hsub0 : (⟨![n, 0], h0⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + ((0 : ℕ) : ℤ)),
          hseg 0 (Nat.zero_le m)⟩ := Subtype.ext e0.symm
  have hsubm : (⟨![n, t], ht⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![n, 0] : Site 2) 1 ((![n, 0] : Site 2) 1 + ((m : ℕ) : ℤ)),
          hseg m le_rfl⟩ := Subtype.ext em.symm
  rw [hsub0, hsubm]; exact hreach





theorem rcm_rightComplement_reaches_rightWall (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {v : Site 2} (hv : v ∈ bac_rightComplement ω n) :
    ∃ (hvc : v ∈ bac_boxMinusL ω n) (h0 : (![n, 0] : Site 2) ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hvc⟩ ⟨![n, 0], h0⟩ := by
  obtain ⟨hvc, y, hyR, hyc, hreach⟩ := hv
  
  obtain ⟨hybox, hy0⟩ := hyR
  rw [mem_rect] at hybox
  obtain ⟨_, _, ht0, htn⟩ := hybox
  
  have hye : y = ![n, y 1] := by
    funext i; fin_cases i
    · simpa using hy0
    · simp
  obtain ⟨h0, ht, hwall⟩ := rcm_rightWall_reaches_in_boxMinusL ω n hnoH
    (by simpa using ht0) (by simpa using htn)
  
  have hyc' : (![n, y 1] : Site 2) ∈ bac_boxMinusL ω n := by rw [← hye]; exact hyc
  have hreach' : ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hvc⟩
      ⟨![n, y 1], hyc'⟩ := by
    have : (⟨y, hyc⟩ : bac_boxMinusL ω n) = ⟨![n, y 1], hyc'⟩ := Subtype.ext hye
    rwa [this] at hreach
  exact ⟨hvc, h0, hreach'.trans hwall.symm⟩



theorem rcm_rightComplement_connected_pair (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {u v : Site 2}
    (hu : u ∈ bac_rightComplement ω n) (hv : v ∈ bac_rightComplement ω n) :
    ∃ (huc : u ∈ bac_boxMinusL ω n) (hvc : v ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨u, huc⟩ ⟨v, hvc⟩ := by
  obtain ⟨huc, h0u, hru⟩ := rcm_rightComplement_reaches_rightWall ω n hnoH hu
  obtain ⟨hvc, h0v, hrv⟩ := rcm_rightComplement_reaches_rightWall ω n hnoH hv
  refine ⟨huc, hvc, hru.trans ?_⟩
  
  have : (⟨![n, 0], h0u⟩ : bac_boxMinusL ω n) = ⟨![n, 0], h0v⟩ := rfl
  rw [this]; exact hrv.symm















def rcm_RCoastConnectedAll (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ f g : Site 2, bac_IsRCoastFace ω n f → bac_IsRCoastFace ω n g →
    (pmd_boxFaceBarrier ω n).Reachable f g






theorem rcm_rCoastConnected_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hall : rcm_RCoastConnectedAll ω n) :
    bac_RCoastConnected ω n := by
  intro c₀ hc₀ f hf
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  have hfront : bac_IsRCoastFace ω n ![c₀, 0] :=
    bac_frontierFace_isRCoast ω n hnoH (le_refl 0) (by omega) hc₀
  exact hall f ![c₀, 0] hf hfront







theorem rcm_all_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : rcm_RCoastConnectedAll ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  intro f g hf hg
  exact (hres c₀ hc₀ f hf).trans (hres c₀ hc₀ g hg).symm




theorem rcm_reachesBottom_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : ccc_FrontierReachesBottom ω n :=
  bac_reachesBottom_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)



theorem rcm_frontierArcReaches_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : crc2_FrontierArcReaches ω n :=
  bac_frontierArcReaches_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)



theorem rcm_faceDualVCrossing_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : pmd_FaceDualVCrossing ω n :=
  bac_faceDualVCrossing_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)




theorem rcm_exhaustivity_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (rcm_faceDualVCrossing_of_all ω n hn hnoH hall)








theorem rcm_wall_RCoastConnectedAll : rcm_RCoastConnectedAll bcc_wallCfg 2 := by
  intro f g hf hg
  obtain ⟨gf, hgf⟩ := hf.1
  obtain ⟨gg, hgg⟩ := hg.1
  obtain ⟨hf0, hf1⟩ := bac_wall_barrierFace_col0 hgf
  obtain ⟨hg0, hg1⟩ := bac_wall_barrierFace_col0 hgg
  have hfe : f = ![0, f 1] := by funext i; fin_cases i <;> simp [hf0]
  have hge : g = ![0, g 1] := by funext i; fin_cases i <;> simp [hg0]
  rw [hfe, hge]
  exact (bac_wall_col0_reaches_origin (by tauto)).trans
    (bac_wall_col0_reaches_origin (by tauto)).symm





theorem rcm_wall_frontierArcReaches : crc2_FrontierArcReaches bcc_wallCfg 2 :=
  rcm_frontierArcReaches_of_all bcc_wallCfg 2 (by norm_num) bcc_noH_wall rcm_wall_RCoastConnectedAll


theorem rcm_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  rcm_faceDualVCrossing_of_all bcc_wallCfg 2 (by norm_num) bcc_noH_wall rcm_wall_RCoastConnectedAll




theorem rcm_wall_rightComplement_connected :
    ∃ (huc : (![1, 0] : Site 2) ∈ bac_boxMinusL bcc_wallCfg 2)
      (hvc : (![2, 0] : Site 2) ∈ bac_boxMinusL bcc_wallCfg 2),
      ((hypercubicLattice 2).induce (bac_boxMinusL bcc_wallCfg 2)).Reachable
        ⟨![1, 0], huc⟩ ⟨![2, 0], hvc⟩ := by
  have hg := bac_wall_gap_mem
  have hwall : (![2, 0] : Site 2) ∈ bac_rightComplement bcc_wallCfg 2 :=
    bac_rightWall_mem_rightComplement bcc_wallCfg 2 bcc_noH_wall (by norm_num) (by norm_num)
  exact rcm_rightComplement_connected_pair bcc_wallCfg 2 bcc_noH_wall hg hwall



theorem rcm_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall

end Universality

end StatMech

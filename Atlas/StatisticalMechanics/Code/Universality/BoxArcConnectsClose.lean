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
import Code.Universality.FaceDualDichotomy
import Code.Universality.FrameChangeIso
import Code.Universality.BoxCrossingDichotomy
import Code.Universality.BoxCrossingDichotomyClose
import Code.Universality.RSWDualVCrossingClose
import Code.Universality.PlanarMengerDualityClose
import Code.Universality.MengerBarrierClose
import Code.Universality.CoastlineContinuityClose
import Code.Universality.CoastlineAnchorClose
import Code.Universality.CircuitReachClose

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality






def bac_boxMinusL (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  rect 0 n 0 n \ bcd_leftReach ω n






def bac_rightComplement (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  {v | ∃ (hv : v ∈ bac_boxMinusL ω n) (y : Site 2) (_hy : y ∈ rightSide 0 n 0 n)
        (hyc : y ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hv⟩ ⟨y, hyc⟩}


theorem bac_rightComplement_subset_boxMinusL (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    bac_rightComplement ω n ⊆ bac_boxMinusL ω n := fun _ hv => hv.choose


theorem bac_rightComplement_mem (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v : Site 2}
    (hv : v ∈ bac_rightComplement ω n) : v ∈ rect 0 n 0 n ∧ v ∉ bcd_leftReach ω n :=
  bac_rightComplement_subset_boxMinusL ω n hv





theorem bac_rightWall_mem_rightComplement (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {r : ℤ} (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    (![n, r] : Site 2) ∈ bac_rightComplement ω n := by
  have hn : 0 ≤ n := le_trans hr0 hrn
  have hyR : (![n, r] : Site 2) ∈ rightSide 0 n 0 n := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  have hyc : (![n, r] : Site 2) ∈ bac_boxMinusL ω n :=
    ⟨rightSide_subset hyR, jex_rightSide_notin_leftReach ω n hnoH hyR⟩
  exact ⟨hyc, ![n, r], hyR, hyc, SimpleGraph.Reachable.refl _⟩





theorem bac_rightSegment_notMem_L (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (htr : mbc_IsRightFrontier ω n c r) {c' : ℤ} (hcc' : c < c') (hc'n : c' ≤ n) :
    (![c', r] : Site 2) ∉ bcd_leftReach ω n :=
  htr.2.2.2 c' hcc' hc'n












theorem bac_gap_mem_rightComplement (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    (![c + 1, r] : Site 2) ∈ bac_rightComplement ω n := by
  obtain ⟨hc0, hcn, _hcL, _hmax⟩ := htr
  
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n - (c + 1))
  
  have hseg : ∀ t : ℕ, t ≤ m →
      Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (t : ℤ))
        ∈ bac_boxMinusL ω n := by
    intro t ht
    have hval : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (t : ℤ))
        = ![c + 1 + (t : ℤ), r] := by
      funext i; fin_cases i <;> simp [Function.update]
    rw [hval]
    have ht' : (t : ℤ) ≤ (m : ℤ) := by exact_mod_cast ht
    refine ⟨?_, ?_⟩
    · rw [mem_rect]
      refine ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩
    · exact bac_rightSegment_notMem_L ω n
        ⟨hc0, hcn, _hcL, _hmax⟩ (by omega) (by omega)
  
  have hreach := segment_connectedWithin (d := 2) (bac_boxMinusL ω n) (0 : Fin 2)
    (![c + 1, r] : Site 2) m hseg
  
  have e0 : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((0 : ℕ) : ℤ))
      = ![c + 1, r] := by funext i; fin_cases i <;> simp [Function.update]
  have em : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (m : ℤ))
      = ![n, r] := by
    funext i
    fin_cases i
    · simp only [Function.update]; simp; omega
    · simp [Function.update]
  
  have hgapc : (![c + 1, r] : Site 2) ∈ bac_boxMinusL ω n := by
    have := hseg 0 (Nat.zero_le m); rwa [e0] at this
  have hnc : (![n, r] : Site 2) ∈ bac_boxMinusL ω n := by
    have := hseg m le_rfl; rwa [em] at this
  have hn : 0 ≤ n := le_trans hr0 hrn
  have hyR : (![n, r] : Site 2) ∈ rightSide 0 n 0 n := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  refine ⟨hgapc, ![n, r], hyR, hnc, ?_⟩
  
  have hsub0 : (⟨![c + 1, r], hgapc⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((0 : ℕ) : ℤ)),
          hseg 0 (Nat.zero_le m)⟩ := Subtype.ext e0.symm
  have hsubm : (⟨![n, r], hnc⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((m : ℕ) : ℤ)),
          hseg m le_rfl⟩ := Subtype.ext em.symm
  rw [hsub0, hsubm]
  exact hreach




theorem bac_frontierFace_lowerRight (c r : ℤ) :
    faceCorner10 c r = ![c + 1, r] := rfl









def bac_IsRCoastFace (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (f : Site 2) : Prop :=
  (∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj f g) ∧
    (∃ p : Site 2, p ∈ bac_rightComplement ω n ∧
      (p = ![f 0, f 1] ∨ p = ![f 0 + 1, f 1] ∨ p = ![f 0, f 1 + 1] ∨ p = ![f 0 + 1, f 1 + 1]))












theorem bac_frontierFace_isRCoast (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    bac_IsRCoastFace ω n ![c, r] := by
  refine ⟨⟨![c, r - 1], ccc_frontierFace_down_adj ω n hr0 hrn htr⟩, ![c + 1, r], ?_, ?_⟩
  · exact bac_gap_mem_rightComplement ω n hnoH hr0 hrn htr
  · 
    right; left; funext i; fin_cases i <;> simp















def bac_RCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (c₀ : ℤ), mbc_IsRightFrontier ω n c₀ 0 →
    ∀ f : Site 2, bac_IsRCoastFace ω n f →
      (pmd_boxFaceBarrier ω n).Reachable f ![c₀, 0]












theorem bac_reachesBottom_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  refine cac_frontierReachesBottom_of_anchor ω n hc0 hcn (le_refl _) (by omega : (-1 : ℤ) ≤ n) ?_
  intro r hr0 hrn c hc
  
  have hreach0 : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c₀, 0] :=
    hres c₀ hc₀ ![c, r] (bac_frontierFace_isRCoast ω n hnoH hr0 hrn hc)
  
  exact hreach0.trans (cac_row0_frontier_reaches_bottom ω n hn hc₀)







theorem bac_frontierArcReaches_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : crc2_FrontierArcReaches ω n :=
  crc2_arc_of_atom ω n hn (bac_reachesBottom_of_rCoastConnected ω n hn hnoH hres)







def bac_BarrierConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ f g : Site 2, (∃ f' : Site 2, (pmd_boxFaceBarrier ω n).Adj f f') →
    (∃ g' : Site 2, (pmd_boxFaceBarrier ω n).Adj g g') →
      (pmd_boxFaceBarrier ω n).Reachable f g








theorem bac_rCoastConnected_of_barrierConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (h : bac_BarrierConnected ω n) : bac_RCoastConnected ω n := by
  intro c₀ hc₀ f hf
  
  have hfront : ∃ g' : Site 2, (pmd_boxFaceBarrier ω n).Adj ![c₀, 0] g' :=
    ⟨![c₀, (0 : ℤ) - 1], ccc_frontierFace_down_adj ω n (le_refl 0) hn hc₀⟩
  exact h f ![c₀, 0] hf.1 hfront





theorem bac_rightComplement_connected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v : Site 2}
    (hv : v ∈ bac_rightComplement ω n) :
    ∃ (y : Site 2) (_hy : y ∈ rightSide 0 n 0 n) (hvc : v ∈ bac_boxMinusL ω n)
      (hyc : y ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨v, hvc⟩ ⟨y, hyc⟩ := by
  obtain ⟨hvc, y, hy, hyc, hreach⟩ := hv
  exact ⟨y, hy, hvc, hyc, hreach⟩






theorem bac_faceDualVCrossing_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : pmd_FaceDualVCrossing ω n :=
  ccc_faceDualVCrossing_of_reachesBottom ω n hn hnoH
    (bac_reachesBottom_of_rCoastConnected ω n hn hnoH hres)





theorem bac_exhaustivity_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (bac_faceDualVCrossing_of_rCoastConnected ω n hn hnoH hres)







theorem bac_wall_leftReach_iff {v : Site 2} (hv : v ∈ rect 0 2 0 2) :
    v ∈ bcd_leftReach bcc_wallCfg 2 ↔ v 0 = 0 := by
  constructor
  · exact rdv_leftReach_wall_x0
  · intro h0
    exact jex_leftSide_subset_leftReach bcc_wallCfg 2 ⟨hv, h0⟩






theorem bac_wall_face_from_horiz_edge {f g : Site 2} {c : ℤ}
    (hadj : (hypercubicLattice 2).Adj f g)
    (hedge : sharedPrimalEdge f g = s(![0, c], ![1, c])) :
    f 0 = 0 ∧ (f 1 = c ∨ f 1 = c - 1) := by
  classical
  
  
  
  unfold sharedPrimalEdge at hedge
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0] at hedge
    
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · 
      have hf0 : f 0 = 0 := by have := congrFun e1 0; simpa using this
      have hM : max (f 1) (g 1) = c := by have := congrFun e1 1; simpa using this
      refine ⟨hf0, ?_⟩
      
      have hadj' := hadj
      rw [hypercubicLattice_adj, Fin.sum_univ_two, h0] at hadj'
      simp only [sub_self, Int.natAbs_zero, zero_add] at hadj'
      have : g 1 = f 1 + 1 ∨ g 1 = f 1 - 1 := by
        rcases Int.natAbs_eq (f 1 - g 1) with he | he <;> omega
      rcases this with hg | hg
      · right; rw [hg, max_eq_right (by omega : f 1 ≤ f 1 + 1)] at hM; omega
      · left; rw [hg, max_eq_left (by omega : f 1 - 1 ≤ f 1)] at hM; omega
    · 
      have ha : f 0 = 1 := by have := congrFun e1 0; simpa using this
      have hb : f 0 + 1 = 0 := by have := congrFun e2 0; simpa using this
      omega
  · rw [if_neg h0] at hedge
    
    
    rw [Sym2.eq_iff] at hedge
    exfalso
    rcases hedge with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have h1 : f 1 = c := by have := congrFun e1 1; simpa using this
      have h2 : f 1 + 1 = c := by have := congrFun e2 1; simpa using this
      omega
    · have h1 : f 1 = c := by have := congrFun e1 1; simpa using this
      have h2 : f 1 + 1 = c := by have := congrFun e2 1; simpa using this
      omega







theorem bac_wall_barrierFace_col0 {f g : Site 2}
    (h : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj f g) :
    f 0 = 0 ∧ (f 1 = -1 ∨ f 1 = 0 ∨ f 1 = 1 ∨ f 1 = 2) := by
  obtain ⟨hadj, p, q, hpq, hbd, hp, hq⟩ := h
  
  have hpadj : (hypercubicLattice 2).Adj p q := by
    obtain ⟨p', q', hpq', hadj'⟩ := sharedPrimalEdge_isLatticeEdge hadj
    rw [hpq'] at hpq; rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · exact hadj'
    · exact hadj'.symm
  rw [bdEdge_mk] at hbd
  
  
  
  have hpq_diff := hpadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq_diff
  rw [mem_rect] at hp hq
  
  by_cases hpL : p ∈ bcd_leftReach bcc_wallCfg 2
  · have hqL : q ∉ bcd_leftReach bcc_wallCfg 2 := (hbd.mp hpL)
    have hp0 : p 0 = 0 := rdv_leftReach_wall_x0 hpL
    have hq0 : q 0 = 1 := by
      have hqne : q 0 ≠ 0 := by
        intro hq00
        exact hqL ((bac_wall_leftReach_iff (by rw [mem_rect]; exact hq)).mpr hq00)
      
      by_contra hne
      have hsamecol : p 0 = q 0 ∨ (p 0 - q 0).natAbs = 1 := by
        rcases Int.natAbs_eq (p 0 - q 0) with he | he <;> omega
      omega
    
    have h1 : p 1 = q 1 := by omega
    
    
    refine ⟨?_, ?_⟩
    · 
      set c := p 1 with hc
      have hpe : p = ![0, c] := by funext i; fin_cases i <;> simp [hp0, hc]
      have hqe : q = ![1, c] := by funext i; fin_cases i <;> simp [hq0, ← h1, hc]
      have hedge : sharedPrimalEdge f g = s(![0, c], ![1, c]) := by rw [hpq, hpe, hqe]
      
      exact bac_wall_face_from_horiz_edge hadj hedge |>.1
    · set c := p 1 with hc
      have hpe : p = ![0, c] := by funext i; fin_cases i <;> simp [hp0, hc]
      have hqe : q = ![1, c] := by funext i; fin_cases i <;> simp [hq0, ← h1, hc]
      have hedge : sharedPrimalEdge f g = s(![0, c], ![1, c]) := by rw [hpq, hpe, hqe]
      have hf := bac_wall_face_from_horiz_edge hadj hedge
      
      have hb : 0 ≤ c ∧ c ≤ 2 := ⟨hp.2.2.1, hp.2.2.2⟩
      rcases hf.2 with h | h <;> omega
  · 
    have hqL : q ∈ bcd_leftReach bcc_wallCfg 2 := by
      by_contra hqn; exact hpL (hbd.mpr hqn)
    have hq0 : q 0 = 0 := rdv_leftReach_wall_x0 hqL
    have hp0 : p 0 = 1 := by
      have hpne : p 0 ≠ 0 := by
        intro hp00
        exact hpL ((bac_wall_leftReach_iff (by rw [mem_rect]; exact hp)).mpr hp00)
      by_contra hne
      have : p 0 = q 0 ∨ (p 0 - q 0).natAbs = 1 := by
        rcases Int.natAbs_eq (p 0 - q 0) with he | he <;> omega
      omega
    have h1 : p 1 = q 1 := by omega
    set c := p 1 with hc
    have hpe : p = ![1, c] := by funext i; fin_cases i <;> simp [hp0, hc]
    have hqe : q = ![0, c] := by funext i; fin_cases i <;> simp [hq0, ← h1, hc]
    have hedge : sharedPrimalEdge f g = s(![0, c], ![1, c]) := by
      rw [hpq, hpe, hqe, Sym2.eq_swap]
    have hf := bac_wall_face_from_horiz_edge hadj hedge
    have hb : 0 ≤ c ∧ c ≤ 2 := ⟨hp.2.2.1, hp.2.2.2⟩
    exact ⟨hf.1, by rcases hf.2 with h | h <;> omega⟩




theorem bac_wall_col0_reaches_origin {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1 ∨ b = 2) :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Reachable ![0, b] ![0, 0] := by
  
  have a1 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (-1 : ℤ)] ![0, (0 : ℤ)] := by
    have h := pmd_wall_barrierVAdj (b := -1) (by tauto)
    rwa [show ((-1 : ℤ) + 1) = (0 : ℤ) from by ring] at h
  have a2 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ)] ![0, (1 : ℤ)] := by
    have h := pmd_wall_barrierVAdj (b := 0) (by tauto)
    rwa [show ((0 : ℤ) + 1) = (1 : ℤ) from by ring] at h
  have a3 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (1 : ℤ)] ![0, (2 : ℤ)] := by
    have h := pmd_wall_barrierVAdj (b := 1) (by tauto)
    rwa [show ((1 : ℤ) + 1) = (2 : ℤ) from by ring] at h
  rcases hb with rfl | rfl | rfl | rfl
  · exact a1.reachable
  · exact Reachable.refl _
  · exact a2.symm.reachable
  · exact (a3.symm.reachable).trans a2.symm.reachable








theorem bac_wall_rCoastConnected : bac_RCoastConnected bcc_wallCfg 2 := by
  intro c₀ hc₀ f hf
  
  have hc₀0 : c₀ = 0 := mbc_wall_rightFrontier_zero hc₀
  subst hc₀0
  
  obtain ⟨g, hg⟩ := hf.1
  obtain ⟨hf0, hf1⟩ := bac_wall_barrierFace_col0 hg
  have hfe : f = ![0, f 1] := by funext i; fin_cases i <;> simp [hf0]
  rw [hfe]
  exact bac_wall_col0_reaches_origin (by tauto)






theorem bac_wall_frontierArcReaches : crc2_FrontierArcReaches bcc_wallCfg 2 :=
  bac_frontierArcReaches_of_rCoastConnected bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    bac_wall_rCoastConnected




theorem bac_wall_reachesBottom : ccc_FrontierReachesBottom bcc_wallCfg 2 :=
  bac_reachesBottom_of_rCoastConnected bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    bac_wall_rCoastConnected




theorem bac_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  bac_faceDualVCrossing_of_rCoastConnected bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    bac_wall_rCoastConnected





theorem bac_wall_gap_mem :
    (![1, 0] : Site 2) ∈ bac_rightComplement bcc_wallCfg 2 := by
  have := bac_gap_mem_rightComplement bcc_wallCfg 2 bcc_noH_wall (c := 0) (r := 0)
    (le_refl 0) (by norm_num) (mbc_wall_rightFrontier_at (le_refl 0) (by norm_num))
  simpa using this



theorem bac_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall

end Universality

end StatMech

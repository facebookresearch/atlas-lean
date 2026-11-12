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
import Code.Universality.MengerBarrierClose
import Code.Universality.CoastlineContinuityClose
import Code.Universality.CoastlineAnchorClose

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality















def crc2_IsBoxInteriorEdge (n : ℤ) (f g : Site 2) : Prop :=
  ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n







theorem crc2_boxBarrier_adj_of_interior (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f g : Site 2}
    (hfb : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    (hint : crc2_IsBoxInteriorEdge n f g) :
    (pmd_boxFaceBarrier ω n).Adj f g := by
  obtain ⟨p, q, hpq, hp, hq⟩ := hint
  refine ⟨hfb.1, p, q, hpq, ?_, hp, hq⟩
  have := faceBoundaryGraph_sharedPrimalEdge_bdEdge _ hfb
  rwa [hpq] at this









theorem crc2_walk_lift (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {u v : Site 2}
    (w : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u v)
    (hint : ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g) :
    (pmd_boxFaceBarrier ω n).Reachable u v := by
  refine ⟨w.transfer (pmd_boxFaceBarrier ω n) ?_⟩
  intro e he
  refine e.ind (fun f g hfg => ?_) he
  rw [SimpleGraph.mem_edgeSet]
  exact crc2_boxBarrier_adj_of_interior ω n (w.adj_of_mem_edges hfg) (hint f g hfg)







theorem crc2_frontier_down_edge_interior (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    crc2_IsBoxInteriorEdge n ![c, r] ![c, r - 1] := by
  obtain ⟨hc0, hcn, _hcL, _hmax⟩ := htr
  refine ⟨![c, r], ![c + 1, r], ?_, ?_, ?_⟩
  · rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; rfl
  · rw [mem_rect]
    exact ⟨by simpa using hc0, by simp; omega, by simpa using hr0, by simpa using hrn⟩
  · rw [mem_rect]
    exact ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩























def crc2_FrontierArcReaches (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (c₀ : ℤ), mbc_IsRightFrontier ω n c₀ 0 →
    ∀ (r : ℤ), 0 ≤ r → r ≤ n → ∀ (c : ℤ), mbc_IsRightFrontier ω n c r →
      ∃ w : (faceBoundaryGraph (bcd_leftReach ω n)).Walk ![c, r] ![c₀, 0],
        ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g













theorem crc2_frontierReachesBottom_of_arc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (harc : crc2_FrontierArcReaches ω n) :
    ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  refine cac_frontierReachesBottom_of_anchor ω n hc0 hcn (le_refl _) (by omega : (-1 : ℤ) ≤ n) ?_
  intro r hr0 hrn c hc
  obtain ⟨w, hw⟩ := harc c₀ hc₀ r hr0 hrn c hc
  
  exact (crc2_walk_lift ω n w hw).trans (cac_row0_frontier_reaches_bottom ω n hn hc₀)















theorem crc2_arc_of_atom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (h : ccc_FrontierReachesBottom ω n) : crc2_FrontierArcReaches ω n := by
  classical
  obtain ⟨a₀, b₀, _, _, _, _, hanchor⟩ := h
  intro c₀ hc₀ r hr0 hrn c hc
  
  have hreachA : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![a₀, b₀] := hanchor r hr0 hrn c hc
  have hreach0 : (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![a₀, b₀] :=
    hanchor 0 (le_refl 0) hn c₀ hc₀
  have hreach : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c₀, 0] := hreachA.trans hreach0.symm
  obtain ⟨wb⟩ := hreach
  
  set wf : (faceBoundaryGraph (bcd_leftReach ω n)).Walk ![c, r] ![c₀, 0] :=
    wb.mapLe (cac_boxFaceBarrier_le_faceBoundaryGraph ω n) with hwf
  refine ⟨wf, ?_⟩
  intro f g hfg
  
  have hadj : (pmd_boxFaceBarrier ω n).Adj f g := by
    have hmap : wf.edges = wb.edges := by
      rw [hwf]; exact SimpleGraph.Walk.edges_mapLe_eq_edges _ _
    rw [hmap] at hfg
    exact wb.adj_of_mem_edges hfg
  obtain ⟨_hlat, p, q, hpq, _hbd, hp, hq⟩ := hadj
  exact ⟨p, q, hpq, hp, hq⟩










theorem crc2_circuit_exists (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c : ℤ}
    (hc0 : 0 ≤ c) (hcn : c ≤ n) :
    ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), cyc.IsCycle :=
  jex_exists_dualCircuit ω hn hnoH hc0 hcn





theorem crc2_barrierConnectsRows_of_arc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (harc : crc2_FrontierArcReaches ω n) :
    pmd_BarrierConnectsRows ω n :=
  ccc_barrierConnectsRows_of_reachesBottom ω n hn hnoH
    (crc2_frontierReachesBottom_of_arc ω n hn hnoH harc)





theorem crc2_faceDualVCrossing_of_arc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (harc : crc2_FrontierArcReaches ω n) :
    pmd_FaceDualVCrossing ω n :=
  ccc_faceDualVCrossing_of_reachesBottom ω n hn hnoH
    (crc2_frontierReachesBottom_of_arc ω n hn hnoH harc)





theorem crc2_exhaustivity_of_arc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (harc : crc2_FrontierArcReaches ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (crc2_faceDualVCrossing_of_arc ω n hn hnoH harc)







theorem crc2_wall_down_edge_interior {r : ℤ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    crc2_IsBoxInteriorEdge 2 ![0, r] ![0, r - 1] :=
  crc2_frontier_down_edge_interior bcc_wallCfg 2 hr0 hr2
    (mbc_wall_rightFrontier_at hr0 hr2)










theorem crc2_wall_frontierArcReaches : crc2_FrontierArcReaches bcc_wallCfg 2 := by
  intro c₀ hc₀ r hr0 hrn c hc
  
  have hc₀0 : c₀ = 0 := mbc_wall_rightFrontier_zero hc₀
  subst hc₀0
  have hc0 : c = 0 := mbc_wall_rightFrontier_zero hc
  subst hc0
  
  have hadj : ∀ s : ℤ, 0 ≤ s → s ≤ 2 →
      (faceBoundaryGraph (bcd_leftReach bcc_wallCfg 2)).Adj ![0, s] ![0, s - 1] :=
    fun s hs0 hs2 =>
      cac_boxFaceBarrier_le_faceBoundaryGraph bcc_wallCfg 2
        (ccc_frontierFace_down_adj bcc_wallCfg 2 hs0 hs2 (mbc_wall_rightFrontier_at hs0 hs2))
  
  set G := faceBoundaryGraph (bcd_leftReach bcc_wallCfg 2) with hG
  
  have hswap : ∀ s : ℤ, 0 ≤ s → s ≤ 2 → crc2_IsBoxInteriorEdge 2 ![0, s - 1] ![0, s] := by
    intro s hs0 hs2
    obtain ⟨p, q, hpq, hp, hq⟩ := crc2_wall_down_edge_interior (r := s) hs0 hs2
    refine ⟨p, q, ?_, hp, hq⟩
    rw [sharedPrimalEdge_comm_of_adj (by simp [hypercubicLattice_adj, Fin.sum_univ_two])]
    simpa using hpq
  interval_cases r
  · 
    exact ⟨SimpleGraph.Walk.nil, by intro f g hfg; simp at hfg⟩
  · 
    have h1 : G.Adj ![0, (1 : ℤ)] ![0, (0 : ℤ)] := by
      have h := hadj 1 (by norm_num) (by norm_num)
      have he : ((1 : ℤ) - 1) = (0 : ℤ) := by ring
      rwa [he] at h
    refine ⟨SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil, ?_⟩
    intro f g hfg
    rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_singleton] at hfg
    rw [Sym2.eq_iff] at hfg
    rcases hfg with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · simpa using crc2_wall_down_edge_interior (r := 1) (by norm_num) (by norm_num)
    · simpa using hswap 1 (by norm_num) (by norm_num)
  · 
    have h2 : G.Adj ![0, (2 : ℤ)] ![0, (1 : ℤ)] := by
      have h := hadj 2 (by norm_num) (by norm_num)
      have he : ((2 : ℤ) - 1) = (1 : ℤ) := by ring
      rwa [he] at h
    have h1 : G.Adj ![0, (1 : ℤ)] ![0, (0 : ℤ)] := by
      have h := hadj 1 (by norm_num) (by norm_num)
      have he : ((1 : ℤ) - 1) = (0 : ℤ) := by ring
      rwa [he] at h
    refine ⟨SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil), ?_⟩
    intro f g hfg
    rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil] at hfg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfg
    rcases hfg with hfg | hfg <;> rw [Sym2.eq_iff] at hfg <;>
      rcases hfg with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · simpa using crc2_wall_down_edge_interior (r := 2) (by norm_num) (by norm_num)
    · simpa using hswap 2 (by norm_num) (by norm_num)
    · simpa using crc2_wall_down_edge_interior (r := 1) (by norm_num) (by norm_num)
    · simpa using hswap 1 (by norm_num) (by norm_num)






theorem crc2_wall_atom : ccc_FrontierReachesBottom bcc_wallCfg 2 :=
  crc2_frontierReachesBottom_of_arc bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crc2_wall_frontierArcReaches






theorem crc2_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  crc2_faceDualVCrossing_of_arc bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crc2_wall_frontierArcReaches



theorem crc2_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall

end Universality

end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































































import Mathlib
import Code.RSW.BoxCrossing
import Code.RSW.Defs
import Code.RSW.SelfDuality
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarDual
import Code.Lattice.JordanEnclosure
import Code.Lattice.SegmentConn
import Code.Lattice.StraightWalk
import Code.Lattice.PeierlsHoleFreeBoundary
import Code.Ising.KWGeometricDual
import Code.Universality.CrossingReflection
import Code.Universality.CrossingTranslationInvariance
import Code.Universality.BXPAllAspect
import Code.Universality.JordanExhaustivityClose
import Code.Universality.PlanarMengerDualityClose
import Code.Universality.MengerBarrierClose
import Code.Universality.CoastlineContinuityClose
import Code.Universality.CoastlineAnchorClose
import Code.Universality.CircuitReachClose
import Code.Universality.BoxArcConnectsClose
import Code.Universality.RCoastMengerClose

open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality








theorem crr_rightComplement_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c c' : Site 2}
    (hc : c ∈ bac_rightComplement ω n) (hadj : (hypercubicLattice 2).Adj c c')
    (hc'box : c' ∈ rect 0 n 0 n) (hc'L : c' ∉ bcd_leftReach ω n) :
    c' ∈ bac_rightComplement ω n := by
  obtain ⟨hcc, y, hyR, hyc, hreach⟩ := hc
  have hc'c : c' ∈ bac_boxMinusL ω n := ⟨hc'box, hc'L⟩
  refine ⟨hc'c, y, hyR, hyc, ?_⟩
  have hstep : ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Adj ⟨c', hc'c⟩ ⟨c, hcc⟩ := by
    simp only [SimpleGraph.induce_adj]; exact hadj.symm
  exact (hstep.reachable).trans hreach






theorem crr_horizInterface_flank0_isRCoast (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
    (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
    bac_IsRCoastFace ω n ![x, y] := by
  refine ⟨⟨![x, y - 1], rcm_horizEdge_faces_pmdAdj ω n hbd hp hq⟩, ![x + 1, y], hqR, ?_⟩
  right; left; simp





theorem crr_horizInterface_flank1_isRCoast (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
    (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
    bac_IsRCoastFace ω n ![x, y - 1] := by
  refine ⟨⟨![x, y], (rcm_horizEdge_faces_pmdAdj ω n hbd hp hq).symm⟩, ![x + 1, y], hqR, ?_⟩
  right; right; right; simp






theorem crr_face_nbr_cases (a b : ℤ) (g : Site 2) (hadj : (hypercubicLattice 2).Adj ![a, b] g) :
    g = ![a + 1, b] ∨ g = ![a - 1, b] ∨ g = ![a, b + 1] ∨ g = ![a, b - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hadj
  have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> simp
  have key : ((a - g 0).natAbs = 1 ∧ (b - g 1).natAbs = 0) ∨
             ((a - g 0).natAbs = 0 ∧ (b - g 1).natAbs = 1) := by omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hb : g 1 = b := by omega
    rcases Int.natAbs_eq (a - g 0) with he | he
    · right; left; rw [hg, show g 0 = a - 1 by omega, hb]
    · left; rw [hg, show g 0 = a + 1 by omega, hb]
  · have ha : g 0 = a := by omega
    rcases Int.natAbs_eq (b - g 1) with he | he
    · right; right; right; rw [hg, show g 1 = b - 1 by omega, ha]
    · right; right; left; rw [hg, show g 1 = b + 1 by omega, ha]





theorem crr_face_barrier_side (ω : ConfigSpace (Sym2 (Site 2))) (n a b : ℤ)
    (h : ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj ![a, b] g) :
    ∃ u v : Site 2,
      ((u = ![a, b] ∧ v = ![a + 1, b]) ∨ (u = ![a, b + 1] ∧ v = ![a + 1, b + 1]) ∨
        (u = ![a, b] ∧ v = ![a, b + 1]) ∨ (u = ![a + 1, b] ∧ v = ![a + 1, b + 1])) ∧
      bdEdge (bcd_leftReach ω n) s(u, v) ∧ u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
  obtain ⟨g, hadj, p, q, hpq, hbd, hp, hq⟩ := h
  
  have finish : ∀ u v : Site 2, sharedPrimalEdge ![a, b] g = s(u, v) →
      bdEdge (bcd_leftReach ω n) s(u, v) ∧ u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
    intro u v hs
    rw [hs] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · exact ⟨hbd, hp, hq⟩
    · exact ⟨by rwa [Sym2.eq_swap], hq, hp⟩
  rcases crr_face_nbr_cases a b g hadj with hg | hg | hg | hg <;> subst hg
  · refine ⟨![a + 1, b], ![a + 1, b + 1], by tauto, finish _ _ ?_⟩
    rw [sharedPrimalEdge_right]; rfl
  · refine ⟨![a, b], ![a, b + 1], by tauto, finish _ _ ?_⟩
    rw [sharedPrimalEdge_left]; rfl
  · refine ⟨![a, b + 1], ![a + 1, b + 1], by tauto, finish _ _ ?_⟩
    rw [sharedPrimalEdge_top]; rfl
  · refine ⟨![a, b], ![a + 1, b], by tauto, finish _ _ ?_⟩
    rw [sharedPrimalEdge_bottom]; rfl






theorem crr_nbr_of_rCorner (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c c' : Site 2}
    (hc : c ∈ bac_rightComplement ω n) (hadj : (hypercubicLattice 2).Adj c c')
    (hc'box : c' ∈ rect 0 n 0 n) :
    c' ∈ bcd_leftReach ω n ∨ c' ∈ bac_rightComplement ω n := by
  by_cases hL : c' ∈ bcd_leftReach ω n
  · exact Or.inl hL
  · exact Or.inr (crr_rightComplement_closed ω n hc hadj hc'box hL)





def crr_HasInterfaceSide (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (f : Site 2) : Prop :=
  ∃ pL pR : Site 2, pL ∈ bcd_leftReach ω n ∧ pR ∈ bac_rightComplement ω n ∧
    (hypercubicLattice 2).Adj pL pR ∧ pL ∈ rect 0 n 0 n ∧ pR ∈ rect 0 n 0 n ∧
    (pL = ![f 0, f 1] ∨ pL = ![f 0 + 1, f 1] ∨ pL = ![f 0, f 1 + 1] ∨ pL = ![f 0 + 1, f 1 + 1]) ∧
    (pR = ![f 0, f 1] ∨ pR = ![f 0 + 1, f 1] ∨ pR = ![f 0, f 1 + 1] ∨ pR = ![f 0 + 1, f 1 + 1])





theorem crr_corner_adj_or_diag {a b : ℤ} {p q : Site 2}
    (hp : p = ![a, b] ∨ p = ![a + 1, b] ∨ p = ![a, b + 1] ∨ p = ![a + 1, b + 1])
    (hq : q = ![a, b] ∨ q = ![a + 1, b] ∨ q = ![a, b + 1] ∨ q = ![a + 1, b + 1])
    (hne : p ≠ q) :
    (hypercubicLattice 2).Adj p q ∨ (p 0 ≠ q 0 ∧ p 1 ≠ q 1) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    solve
      | (exact absurd rfl hne)
      | (left; omega)
      | (right; refine ⟨?_, ?_⟩ <;> omega)













theorem crr_rCoastFace_has_interface_side (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {f : Site 2} (hf : bac_IsRCoastFace ω n f) :
    crr_HasInterfaceSide ω n f := by
  obtain ⟨hbarr, c, hcR, hcCorner⟩ := hf
  
  set a := f 0 with ha
  set b := f 1 with hb
  
  obtain ⟨u, v, hsides, hbd, hu, hv⟩ := crr_face_barrier_side ω n a b (by
    obtain ⟨g, hg⟩ := hbarr
    refine ⟨g, ?_⟩
    have : (![a, b] : Site 2) = f := by funext i; fin_cases i <;> simp [ha, hb]
    rwa [this])
  
  have huv_adj : (hypercubicLattice 2).Adj u v := by
    rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have huCorner : u = ![a, b] ∨ u = ![a + 1, b] ∨ u = ![a, b + 1] ∨ u = ![a + 1, b + 1] := by
    rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  have hvCorner : v = ![a, b] ∨ v = ![a + 1, b] ∨ v = ![a, b + 1] ∨ v = ![a + 1, b + 1] := by
    rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  
  rw [bdEdge_mk] at hbd
  
  have hcCorner' : c = ![a, b] ∨ c = ![a + 1, b] ∨ c = ![a, b + 1] ∨ c = ![a + 1, b + 1] := by
    simpa [ha, hb] using hcCorner
  
  
  have mk : ∀ pL pR : Site 2, pL ∈ bcd_leftReach ω n → pR ∈ bac_rightComplement ω n →
      (hypercubicLattice 2).Adj pL pR → pL ∈ rect 0 n 0 n → pR ∈ rect 0 n 0 n →
      (pL = ![a, b] ∨ pL = ![a + 1, b] ∨ pL = ![a, b + 1] ∨ pL = ![a + 1, b + 1]) →
      (pR = ![a, b] ∨ pR = ![a + 1, b] ∨ pR = ![a, b + 1] ∨ pR = ![a + 1, b + 1]) →
      crr_HasInterfaceSide ω n f := by
    intro pL pR h1 h2 h3 h4 h5 h6 h7
    exact ⟨pL, pR, h1, h2, h3, h4, h5, by simpa [ha, hb] using h6, by simpa [ha, hb] using h7⟩
  
  by_cases huL : u ∈ bcd_leftReach ω n
  · 
    have hvnL : v ∉ bcd_leftReach ω n := hbd.mp huL
    by_cases hvR : v ∈ bac_rightComplement ω n
    · 
      exact mk u v huL hvR huv_adj hu hv huCorner hvCorner
    · 
      have hcv : c ≠ v := fun h => hvR (h ▸ hcR)
      have hnotadj : ¬ (hypercubicLattice 2).Adj c v := fun hadj =>
        hvR (crr_rightComplement_closed ω n hcR hadj hv hvnL)
      
      rcases crr_corner_adj_or_diag hcCorner' hvCorner hcv with hadj | hdiag
      · exact absurd hadj hnotadj
      · 
        have hcu_adj : (hypercubicLattice 2).Adj c u := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at huv_adj ⊢
          obtain ⟨hd0, hd1⟩ := hdiag
          rcases huCorner with rfl | rfl | rfl | rfl <;>
            rcases hvCorner with rfl | rfl | rfl | rfl <;>
            rcases hcCorner' with rfl | rfl | rfl | rfl <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at huv_adj hd0 hd1 ⊢ <;> omega
        have hcbox : c ∈ rect 0 n 0 n := (bac_rightComplement_mem ω n hcR).1
        exact mk u c huL hcR hcu_adj.symm hu hcbox huCorner hcCorner'
  · 
    have hvL : v ∈ bcd_leftReach ω n := by
      by_cases hvL : v ∈ bcd_leftReach ω n
      · exact hvL
      · exact absurd (hbd.mpr hvL) huL
    have hunL : u ∉ bcd_leftReach ω n := huL
    by_cases huR : u ∈ bac_rightComplement ω n
    · exact mk v u hvL huR huv_adj.symm hv hu hvCorner huCorner
    · have hcu : c ≠ u := fun h => huR (h ▸ hcR)
      have hnotadj : ¬ (hypercubicLattice 2).Adj c u := fun hadj =>
        huR (crr_rightComplement_closed ω n hcR hadj hu hunL)
      rcases crr_corner_adj_or_diag hcCorner' huCorner hcu with hadj | hdiag
      · exact absurd hadj hnotadj
      · have hcv_adj : (hypercubicLattice 2).Adj c v := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at huv_adj ⊢
          obtain ⟨hd0, hd1⟩ := hdiag
          rcases huCorner with rfl | rfl | rfl | rfl <;>
            rcases hvCorner with rfl | rfl | rfl | rfl <;>
            rcases hcCorner' with rfl | rfl | rfl | rfl <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at huv_adj hd0 hd1 ⊢ <;> omega
        have hcbox : c ∈ rect 0 n 0 n := (bac_rightComplement_mem ω n hcR).1
        exact mk v c hvL hcR hcv_adj.symm hv hcbox hvCorner hcCorner'






theorem crr_hasInterfaceSide_pmdVertex (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f : Site 2}
    (h : crr_HasInterfaceSide ω n f) : ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj f g := by
  obtain ⟨pL, pR, hpL, hpR, hadj, hpLbox, hpRbox, hpLc, hpRc⟩ := h
  have hbd : bdEdge (bcd_leftReach ω n) s(pL, pR) :=
    rcm_LR_edge_bdEdge ω n hpL hpR
  
  set a := f 0 with ha
  set b := f 1 with hb
  have hfe : f = ![a, b] := by funext i; fin_cases i <;> simp [ha, hb]
  
  rcases hpLc with rfl | rfl | rfl | rfl <;> rcases hpRc with rfl | rfl | rfl | rfl <;>
    first
      | (exfalso; revert hadj; rw [hypercubicLattice_adj, Fin.sum_univ_two];
         simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
      
      | (rw [hfe]; exact ⟨![a, b - 1], rcm_horizEdge_faces_pmdAdj ω n hbd hpLbox hpRbox⟩)
      | (rw [hfe]; exact ⟨![a, b - 1],
          (rcm_horizEdge_faces_pmdAdj ω n (by rwa [Sym2.eq_swap] at hbd) hpRbox hpLbox)⟩)
      
      | (rw [hfe]; refine ⟨![a, b + 1], ?_⟩;
         have := rcm_horizEdge_faces_pmdAdj ω n (x := a) (y := b + 1) hbd hpLbox hpRbox;
         simpa using this.symm)
      | (rw [hfe]; refine ⟨![a, b + 1], ?_⟩;
         have := rcm_horizEdge_faces_pmdAdj ω n (x := a) (y := b + 1)
           (by rwa [Sym2.eq_swap] at hbd) hpRbox hpLbox;
         simpa using this.symm)
      
      | (rw [hfe]; exact ⟨![a - 1, b], rcm_vertEdge_faces_pmdAdj ω n hbd hpLbox hpRbox⟩)
      | (rw [hfe]; exact ⟨![a - 1, b],
          rcm_vertEdge_faces_pmdAdj ω n (by rwa [Sym2.eq_swap] at hbd) hpRbox hpLbox⟩)
      
      | (rw [hfe]; refine ⟨![a + 1, b], ?_⟩;
         have := rcm_vertEdge_faces_pmdAdj ω n (x := a + 1) (y := b) hbd hpLbox hpRbox;
         simpa using this.symm)
      | (rw [hfe]; refine ⟨![a + 1, b], ?_⟩;
         have := rcm_vertEdge_faces_pmdAdj ω n (x := a + 1) (y := b)
           (by rwa [Sym2.eq_swap] at hbd) hpRbox hpLbox;
         simpa using this.symm)






def crr_InterfaceSideWith (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (f q : Site 2) : Prop :=
  q ∈ bac_rightComplement ω n ∧
    ∃ pL : Site 2, pL ∈ bcd_leftReach ω n ∧
      (hypercubicLattice 2).Adj pL q ∧ pL ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n ∧
      (pL = ![f 0, f 1] ∨ pL = ![f 0 + 1, f 1] ∨ pL = ![f 0, f 1 + 1] ∨ pL = ![f 0 + 1, f 1 + 1]) ∧
      (q = ![f 0, f 1] ∨ q = ![f 0 + 1, f 1] ∨ q = ![f 0, f 1 + 1] ∨ q = ![f 0 + 1, f 1 + 1])



theorem crr_hasInterfaceSide_of_with (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f q : Site 2}
    (h : crr_InterfaceSideWith ω n f q) : crr_HasInterfaceSide ω n f := by
  obtain ⟨hqR, pL, hpL, hadj, hpLbox, hqbox, hpLc, hqc⟩ := h
  exact ⟨pL, q, hpL, hqR, hadj, hpLbox, hqbox, hpLc, hqc⟩




theorem crr_rCoastFace_interfaceSideWith (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f : Site 2}
    (hf : bac_IsRCoastFace ω n f) : ∃ q : Site 2, crr_InterfaceSideWith ω n f q := by
  obtain ⟨pL, pR, hpL, hpR, hadj, hpLbox, hpRbox, hpLc, hpRc⟩ :=
    crr_rCoastFace_has_interface_side ω n hf
  exact ⟨pR, hpR, pL, hpL, hadj, hpLbox, hpRbox, hpLc, hpRc⟩















def crr_InterfaceCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (f₁ f₂ q₁ q₂ : Site 2),
    crr_InterfaceSideWith ω n f₁ q₁ → crr_InterfaceSideWith ω n f₂ q₂ →
    ∀ (h1 : q₁ ∈ bac_boxMinusL ω n) (h2 : q₂ ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨q₁, h1⟩ ⟨q₂, h2⟩ →
      (pmd_boxFaceBarrier ω n).Reachable f₁ f₂






theorem crr_frontierFace_interfaceSideWith (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c₀ : ℤ}
    (hc₀ : mbc_IsRightFrontier ω n c₀ 0) :
    crr_InterfaceSideWith ω n ![c₀, 0] ![c₀ + 1, 0] := by
  obtain ⟨hc0, hcn, hcL, _hmax⟩ := id hc₀
  have hgapR : (![c₀ + 1, 0] : Site 2) ∈ bac_rightComplement ω n :=
    bac_gap_mem_rightComplement ω n hnoH (le_refl 0) hn hc₀
  refine ⟨hgapR, ![c₀, 0], hcL, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hypercubicLattice_adj, Fin.sum_univ_two]
  · rw [mem_rect]; exact ⟨by simpa using hc0, by simp; omega, by simp, by simpa using hn⟩
  · rw [mem_rect]; exact ⟨by simp; omega, by simp; omega, by simp, by simpa using hn⟩
  · left; simp
  · right; left; simp














theorem crr_rCoastConnected_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) : bac_RCoastConnected ω n := by
  intro c₀ hc₀ f hf
  
  have hfront : crr_InterfaceSideWith ω n ![c₀, 0] ![c₀ + 1, 0] :=
    crr_frontierFace_interfaceSideWith ω n hn hnoH hc₀
  
  obtain ⟨qf, hqf⟩ := crr_rCoastFace_interfaceSideWith ω n hf
  
  have hqfR : qf ∈ bac_rightComplement ω n := hqf.1
  have hgapR : (![c₀ + 1, 0] : Site 2) ∈ bac_rightComplement ω n := hfront.1
  
  obtain ⟨hqfc, hgapc, hreach⟩ :=
    rcm_rightComplement_connected_pair ω n hnoH hqfR hgapR
  
  exact hres f ![c₀, 0] qf ![c₀ + 1, 0] hqf hfront hqfc hgapc hreach





theorem crr_frontierArcReaches_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) : crc2_FrontierArcReaches ω n :=
  bac_frontierArcReaches_of_rCoastConnected ω n hn hnoH
    (crr_rCoastConnected_of_residue ω n hn hnoH hres)



theorem crr_faceDualVCrossing_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) : pmd_FaceDualVCrossing ω n :=
  bac_faceDualVCrossing_of_rCoastConnected ω n hn hnoH
    (crr_rCoastConnected_of_residue ω n hn hnoH hres)



theorem crr_reachesBottom_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) : ccc_FrontierReachesBottom ω n :=
  bac_reachesBottom_of_rCoastConnected ω n hn hnoH
    (crr_rCoastConnected_of_residue ω n hn hnoH hres)




theorem crr_exhaustivity_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (crr_faceDualVCrossing_of_residue ω n hn hnoH hres)










theorem crr_residue_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : crr_InterfaceCoastConnected ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  intro f₁ f₂ q₁ q₂ h1 h2 _ _ _
  
  have hr1 : bac_IsRCoastFace ω n f₁ := by
    refine ⟨crr_hasInterfaceSide_pmdVertex ω n (crr_hasInterfaceSide_of_with ω n h1), q₁, h1.1, ?_⟩
    obtain ⟨_, _, _, _, _, _, hqc⟩ := h1; tauto
  have hr2 : bac_IsRCoastFace ω n f₂ := by
    refine ⟨crr_hasInterfaceSide_pmdVertex ω n (crr_hasInterfaceSide_of_with ω n h2), q₂, h2.1, ?_⟩
    obtain ⟨_, _, _, _, _, _, hqc⟩ := h2; tauto
  exact (hres c₀ hc₀ f₁ hr1).trans (hres c₀ hc₀ f₂ hr2).symm







theorem crr_wall_interfaceCoastConnected : crr_InterfaceCoastConnected bcc_wallCfg 2 := by
  intro f₁ f₂ q₁ q₂ h1 h2 _ _ _
  
  have hr1 : ∃ g : Site 2, (pmd_boxFaceBarrier bcc_wallCfg 2).Adj f₁ g :=
    crr_hasInterfaceSide_pmdVertex bcc_wallCfg 2 (crr_hasInterfaceSide_of_with bcc_wallCfg 2 h1)
  have hr2 : ∃ g : Site 2, (pmd_boxFaceBarrier bcc_wallCfg 2).Adj f₂ g :=
    crr_hasInterfaceSide_pmdVertex bcc_wallCfg 2 (crr_hasInterfaceSide_of_with bcc_wallCfg 2 h2)
  obtain ⟨g1, hg1⟩ := hr1
  obtain ⟨g2, hg2⟩ := hr2
  obtain ⟨hf10, hf11⟩ := bac_wall_barrierFace_col0 hg1
  obtain ⟨hf20, hf21⟩ := bac_wall_barrierFace_col0 hg2
  have hfe1 : f₁ = ![0, f₁ 1] := by funext i; fin_cases i <;> simp [hf10]
  have hfe2 : f₂ = ![0, f₂ 1] := by funext i; fin_cases i <;> simp [hf20]
  rw [hfe1, hfe2]
  exact (bac_wall_col0_reaches_origin (by tauto)).trans
    (bac_wall_col0_reaches_origin (by tauto)).symm





theorem crr_wall_frontierArcReaches : crc2_FrontierArcReaches bcc_wallCfg 2 :=
  crr_frontierArcReaches_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crr_wall_interfaceCoastConnected


theorem crr_wall_rCoastConnected : bac_RCoastConnected bcc_wallCfg 2 :=
  crr_rCoastConnected_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crr_wall_interfaceCoastConnected


theorem crr_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  crr_faceDualVCrossing_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crr_wall_interfaceCoastConnected



theorem crr_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall










def crr_leftFill (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) : Set (Site 2) :=
  rect 0 n 0 n \ bac_rightComplement omega n



theorem crr_leftReach_openWalk_lift (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    {u v : rect 0 n 0 n} (hu : (u : Site 2) ∈ bcd_leftReach omega n)
    (w : (openSubgraphInduce 2 omega (rect 0 n 0 n)).Walk u v) :
    ∃ hv : (v : Site 2) ∈ bcd_leftReach omega n,
      ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact ⟨hu, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have habOpen : (openSubgraph 2 omega).Adj (a : Site 2) (b : Site 2) := hab
      have hb : (b : Site 2) ∈ bcd_leftReach omega n :=
        bcd_leftReach_extend omega n hu b.2 (openSubgraph_le omega habOpen) habOpen.2
      obtain ⟨hc, hbc⟩ := ih hb
      have habL : ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Adj
          ⟨a, hu⟩ ⟨b, hb⟩ := by
        exact openSubgraph_le omega habOpen
      exact ⟨hc, habL.reachable.trans hbc⟩


theorem crr_leftWall_reaches_zero (omega : ConfigSpace (Sym2 (Site 2))) (n r : Int)
    (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    ∃ (hr : (![0, r] : Site 2) ∈ bcd_leftReach omega n)
      (h0 : (![0, 0] : Site 2) ∈ bcd_leftReach omega n),
      ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable
        ⟨![0, r], hr⟩ ⟨![0, 0], h0⟩ := by
  have hn : 0 ≤ n := hr0.trans hrn
  have hmem : ∀ t : Int, 0 ≤ t → t ≤ n →
      (![0, t] : Site 2) ∈ bcd_leftReach omega n := by
    intro t ht0 htn
    apply jex_leftSide_subset_leftReach omega n
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    exact ⟨by simp [hn], by simp [hn], by simpa using ht0, by simpa using htn⟩
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hr0
  have hseg : ∀ k : Nat, k ≤ m →
      Function.update (![0, 0] : Site 2) 1 ((![0, 0] : Site 2) 1 + (k : Int))
        ∈ bcd_leftReach omega n := by
    intro k hk
    have hval : Function.update (![0, 0] : Site 2) 1
        ((![0, 0] : Site 2) 1 + (k : Int)) = ![0, (k : Int)] := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hval]
    have hk' : (k : Int) ≤ (m : Int) := by exact_mod_cast hk
    exact hmem (k : Int) (by positivity) (by omega)
  have hreach := segment_connectedWithin (d := 2) (bcd_leftReach omega n) (1 : Fin 2)
    (![0, 0] : Site 2) m hseg
  have e0 : Function.update (![0, 0] : Site 2) 1
      ((![0, 0] : Site 2) 1 + ((0 : Nat) : Int)) = ![0, 0] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have em : Function.update (![0, 0] : Site 2) 1
      ((![0, 0] : Site 2) 1 + (m : Int)) = ![0, r] := by
    funext i
    fin_cases i
    · simp [Function.update]
    · simp only [Function.update]
      simp
      omega
  have h0 := hmem 0 le_rfl hn
  have hr := hmem r hr0 hrn
  have hsub0 : (⟨![0, 0], h0⟩ : bcd_leftReach omega n) =
      ⟨Function.update (![0, 0] : Site 2) 1
        ((![0, 0] : Site 2) 1 + ((0 : Nat) : Int)), hseg 0 (Nat.zero_le m)⟩ :=
    Subtype.ext e0.symm
  have hsubm : (⟨![0, r], hr⟩ : bcd_leftReach omega n) =
      ⟨Function.update (![0, 0] : Site 2) 1
        ((![0, 0] : Site 2) 1 + (m : Int)), hseg m le_rfl⟩ :=
    Subtype.ext em.symm
  refine ⟨hr, h0, ?_⟩
  rw [hsub0, hsubm]
  exact hreach.symm



theorem crr_leftReach_connected_pair (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    {u v : Site 2} (hu : u ∈ bcd_leftReach omega n) (hv : v ∈ bcd_leftReach omega n) :
    ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨_hubox, xu, hxu, hubox, hxuReach⟩ := hu
  obtain ⟨_hvbox, xv, hxv, hvbox, hxvReach⟩ := hv
  have hxueq : xu = ![0, xu 1] := by
    funext i
    fin_cases i
    · simpa using hxu.2
    · simp
  have hxveq : xv = ![0, xv 1] := by
    funext i
    fin_cases i
    · simpa using hxv.2
    · simp
  have hxub := mem_rect.mp hxu.1
  have hxvb := mem_rect.mp hxv.1
  obtain ⟨hxuL, hxu0, hxuTo0⟩ :=
    crr_leftWall_reaches_zero omega n (xu 1) hxub.2.2.1 hxub.2.2.2
  obtain ⟨hxvL, hxv0, hxvTo0⟩ :=
    crr_leftWall_reaches_zero omega n (xv 1) hxvb.2.2.1 hxvb.2.2.2
  have hxuL' : xu ∈ bcd_leftReach omega n := by rw [hxueq]; exact hxuL
  have hxvL' : xv ∈ bcd_leftReach omega n := by rw [hxveq]; exact hxvL
  have hxuSub : (⟨xu, hxuL'⟩ : bcd_leftReach omega n) = ⟨![0, xu 1], hxuL⟩ :=
    Subtype.ext hxueq
  have hxvSub : (⟨xv, hxvL'⟩ : bcd_leftReach omega n) = ⟨![0, xv 1], hxvL⟩ :=
    Subtype.ext hxveq
  have hxuTo0' : ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable
      ⟨xu, hxuL'⟩ ⟨![0, 0], hxu0⟩ := by rw [hxuSub]; exact hxuTo0
  have hxvTo0' : ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable
      ⟨xv, hxvL'⟩ ⟨![0, 0], hxv0⟩ := by rw [hxvSub]; exact hxvTo0
  obtain ⟨hu', hxuToU⟩ := crr_leftReach_openWalk_lift omega n hxuL' hxuReach.some
  obtain ⟨hv', hxvToV⟩ := crr_leftReach_openWalk_lift omega n hxvL' hxvReach.some
  have hzero : (⟨![0, 0], hxu0⟩ : bcd_leftReach omega n) = ⟨![0, 0], hxv0⟩ := rfl
  rw [hzero] at hxuTo0'
  have hmid := hxuToU.symm.trans (hxuTo0'.trans (hxvTo0'.symm.trans hxvToV))
  exact hmid


theorem crr_leftWall_reaches_boxVertex (n : Int) {u : Site 2}
    (hu : u ∈ rect 0 n 0 n) :
    ∃ hl : (![0, u 1] : Site 2) ∈ rect 0 n 0 n,
      ((hypercubicLattice 2).induce (rect 0 n 0 n)).Reachable
        ⟨![0, u 1], hl⟩ ⟨u, hu⟩ := by
  have hub := mem_rect.mp hu
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hub.1
  have hseg : ∀ k : Nat, k ≤ m →
      Function.update (![0, u 1] : Site 2) 0
        ((![0, u 1] : Site 2) 0 + (k : Int)) ∈ rect 0 n 0 n := by
    intro k hk
    have hval : Function.update (![0, u 1] : Site 2) 0
        ((![0, u 1] : Site 2) 0 + (k : Int)) = ![(k : Int), u 1] := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hval, mem_rect]
    have hk' : (k : Int) ≤ (m : Int) := by exact_mod_cast hk
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hreach := segment_connectedWithin (d := 2) (rect 0 n 0 n) (0 : Fin 2)
    (![0, u 1] : Site 2) m hseg
  have e0 : Function.update (![0, u 1] : Site 2) 0
      ((![0, u 1] : Site 2) 0 + ((0 : Nat) : Int)) = ![0, u 1] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have em : Function.update (![0, u 1] : Site 2) 0
      ((![0, u 1] : Site 2) 0 + (m : Int)) = u := by
    funext i
    fin_cases i
    · simp only [Function.update]
      simp
      omega
    · simp [Function.update]
  have hl : (![0, u 1] : Site 2) ∈ rect 0 n 0 n := by
    rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by omega, by omega, hub.2.2.1, hub.2.2.2⟩
  have hsub0 : (⟨![0, u 1], hl⟩ : rect 0 n 0 n) =
      ⟨Function.update (![0, u 1] : Site 2) 0
        ((![0, u 1] : Site 2) 0 + ((0 : Nat) : Int)), hseg 0 (Nat.zero_le m)⟩ :=
    Subtype.ext e0.symm
  have hsubm : (⟨u, hu⟩ : rect 0 n 0 n) =
      ⟨Function.update (![0, u 1] : Site 2) 0
        ((![0, u 1] : Site 2) 0 + (m : Int)), hseg m le_rfl⟩ :=
    Subtype.ext em.symm
  refine ⟨hl, ?_⟩
  rw [hsub0, hsubm]
  exact hreach



theorem crr_walk_exit_set_in_box (A B : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hw : ∀ z ∈ w.support, z ∈ B) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ a b : Site 2, (hypercubicLattice 2).Adj a b ∧ a ∈ A ∧ b ∉ A ∧ a ∈ B ∧ b ∈ B := by
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ A
      · exact ih (fun z hz => hw z (by simp [hz])) hb hy
      · exact ⟨a, b, hab, hx, hb, hw a (by simp), hw b (by simp)⟩


theorem crr_rightComplement_of_boxMinusL_reachable
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {u v : Site 2}
    (hu : u ∈ bac_boxMinusL omega n) (hv : v ∈ bac_boxMinusL omega n)
    (huv : ((hypercubicLattice 2).induce (bac_boxMinusL omega n)).Reachable
      ⟨u, hu⟩ ⟨v, hv⟩)
    (hvR : v ∈ bac_rightComplement omega n) : u ∈ bac_rightComplement omega n := by
  obtain ⟨_hvc, y, hyR, hyc, hvy⟩ := hvR
  exact ⟨hu, y, hyR, hyc, huv.trans hvy⟩


theorem crr_leftFill_reaches_leftReach
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {u : Site 2}
    (hu : u ∈ crr_leftFill omega n) :
    ∃ z : Site 2, ∃ hzL : z ∈ bcd_leftReach omega n,
      ((hypercubicLattice 2).induce (crr_leftFill omega n)).Reachable
        ⟨u, hu⟩ ⟨z, ⟨bcd_leftReach_subset_box omega n hzL,
          fun hzR => (bac_rightComplement_mem omega n hzR).2 hzL⟩⟩ := by
  by_cases huL : u ∈ bcd_leftReach omega n
  · exact ⟨u, huL, SimpleGraph.Reachable.refl _⟩
  have huB : u ∈ bac_boxMinusL omega n := ⟨hu.1, huL⟩
  let A : Set (Site 2) := {z | ∃ hz : z ∈ bac_boxMinusL omega n,
    ((hypercubicLattice 2).induce (bac_boxMinusL omega n)).Reachable ⟨u, huB⟩ ⟨z, hz⟩}
  have huA : u ∈ A := ⟨huB, SimpleGraph.Reachable.refl _⟩
  obtain ⟨hlbox, hrow⟩ := crr_leftWall_reaches_boxVertex n hu.1
  let ell : Site 2 := ![0, u 1]
  have hellL : ell ∈ bcd_leftReach omega n := by
    apply jex_leftSide_subset_leftReach omega n
    exact ⟨hlbox, by simp [ell]⟩
  have hellA : ell ∉ A := by
    rintro ⟨hellB, _⟩
    exact hellB.2 hellL
  obtain ⟨wrow⟩ := hrow.symm
  let wrowLat : (hypercubicLattice 2).Walk u ell :=
    wrow.map (SimpleGraph.Embedding.induce (rect 0 n 0 n)).toHom
  have hwbox : ∀ z ∈ wrowLat.support, z ∈ rect 0 n 0 n := by
    intro z hz
    change z ∈ (wrow.map
      (SimpleGraph.Embedding.induce (rect 0 n 0 n)).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _hz', rfl⟩ := List.mem_map.mp hz
    exact z'.2
  obtain ⟨a, b, hab, haA, hbA, habox, hbbox⟩ :=
    crr_walk_exit_set_in_box A (rect 0 n 0 n) wrowLat hwbox huA hellA
  obtain ⟨haB, hua⟩ := haA
  have hbL : b ∈ bcd_leftReach omega n := by
    by_contra hbL
    have hbB : b ∈ bac_boxMinusL omega n := ⟨hbbox, hbL⟩
    have hstep : ((hypercubicLattice 2).induce (bac_boxMinusL omega n)).Adj
        ⟨a, haB⟩ ⟨b, hbB⟩ := hab
    exact hbA ⟨hbB, hua.trans hstep.reachable⟩
  have haNotR : a ∉ bac_rightComplement omega n := by
    intro haR
    exact hu.2 (crr_rightComplement_of_boxMinusL_reachable omega n huB haB hua haR)
  obtain ⟨pua⟩ := hua
  let puaLat : (hypercubicLattice 2).Walk u a :=
    pua.map (SimpleGraph.Embedding.induce (bac_boxMinusL omega n)).toHom
  have hpuaFill : ∀ z ∈ puaLat.support, z ∈ crr_leftFill omega n := by
    intro z hz
    change z ∈ (pua.map
      (SimpleGraph.Embedding.induce (bac_boxMinusL omega n)).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    refine ⟨z'.2.1, ?_⟩
    intro hzR
    have huz := (pua.takeUntil z' hz').reachable
    exact hu.2 (crr_rightComplement_of_boxMinusL_reachable omega n huB z'.2 huz hzR)
  have haFill : a ∈ crr_leftFill omega n := ⟨habox, haNotR⟩
  have huaFill : ((hypercubicLattice 2).induce (crr_leftFill omega n)).Reachable
      ⟨u, hu⟩ ⟨a, haFill⟩ :=
    walk_induce_reachable (hypercubicLattice 2) (crr_leftFill omega n) puaLat
      hpuaFill hu haFill
  have hbFill : b ∈ crr_leftFill omega n :=
    ⟨hbbox, fun hbR => (bac_rightComplement_mem omega n hbR).2 hbL⟩
  have habFill : ((hypercubicLattice 2).induce (crr_leftFill omega n)).Adj
      ⟨a, haFill⟩ ⟨b, hbFill⟩ := hab
  exact ⟨b, hbL, huaFill.trans habFill.reachable⟩


theorem crr_leftFill_connected_pair (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    {u v : Site 2} (hu : u ∈ crr_leftFill omega n) (hv : v ∈ crr_leftFill omega n) :
    ((hypercubicLattice 2).induce (crr_leftFill omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨zu, hzuL, huz⟩ := crr_leftFill_reaches_leftReach omega n hu
  obtain ⟨zv, hzvL, hvz⟩ := crr_leftFill_reaches_leftReach omega n hv
  have hLR := crr_leftReach_connected_pair omega n hzuL hzvL
  obtain ⟨pLR⟩ := hLR
  let pFill : (hypercubicLattice 2).Walk zu zv :=
    (pLR.map (SimpleGraph.Embedding.induce (bcd_leftReach omega n)).toHom).mapLe
      (fun _ _ h => h)
  have hpFill : ∀ z ∈ pFill.support, z ∈ crr_leftFill omega n := by
    intro z hz
    have hz' : z ∈ (pLR.map
        (SimpleGraph.Embedding.induce (bcd_leftReach omega n)).toHom).support := by
      simpa [pFill] using hz
    rw [SimpleGraph.Walk.support_map] at hz'
    obtain ⟨z', _hz', rfl⟩ := List.mem_map.mp hz'
    exact ⟨bcd_leftReach_subset_box omega n z'.2,
      fun hzR => (bac_rightComplement_mem omega n hzR).2 z'.2⟩
  have hzuFill : zu ∈ crr_leftFill omega n :=
    ⟨bcd_leftReach_subset_box omega n hzuL,
      fun hzR => (bac_rightComplement_mem omega n hzR).2 hzuL⟩
  have hzvFill : zv ∈ crr_leftFill omega n :=
    ⟨bcd_leftReach_subset_box omega n hzvL,
      fun hzR => (bac_rightComplement_mem omega n hzR).2 hzvL⟩
  have hmiddle := walk_induce_reachable (hypercubicLattice 2) (crr_leftFill omega n)
    pFill hpFill hzuFill hzvFill
  exact huz.trans (hmiddle.trans hvz.symm)


theorem crr_rightComplement_connected_induced
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) {u v : Site 2}
    (hu : u ∈ bac_rightComplement omega n) (hv : v ∈ bac_rightComplement omega n) :
    ((hypercubicLattice 2).induce (bac_rightComplement omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨huB, hvB, huv⟩ := rcm_rightComplement_connected_pair omega n hnoH hu hv
  obtain ⟨p⟩ := huv
  let pLat : (hypercubicLattice 2).Walk u v :=
    p.map (SimpleGraph.Embedding.induce (bac_boxMinusL omega n)).toHom
  have hpR : ∀ z ∈ pLat.support, z ∈ bac_rightComplement omega n := by
    intro z hz
    change z ∈ (p.map
      (SimpleGraph.Embedding.induce (bac_boxMinusL omega n)).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    have hzv := (p.dropUntil z' hz').reachable
    exact crr_rightComplement_of_boxMinusL_reachable omega n z'.2 hvB hzv hv
  exact walk_induce_reachable (hypercubicLattice 2) (bac_rightComplement omega n)
    pLat hpR hu hv


@[reducible] noncomputable def crr_boxPlanar (n : Int) : PlanarZ2Subgraph where
  V := rect 0 n 0 n
  finV := (rect_finite 0 n 0 n).to_subtype
  decV := Classical.decEq _
  G := (hypercubicLattice 2).induce (rect 0 n 0 n)
  emb := ⟨fun v => v.1, Subtype.val_injective⟩
  isSub := fun _ _ h => h

noncomputable instance crr_boxEdgeFinite (n : Int) :
    Finite (Ising.kwg_Edge (crr_boxPlanar n)) :=
  Ising.kwg_edgeFinite (crr_boxPlanar n)


noncomputable def crr_boxRColour (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    (crr_boxPlanar n).V → Bool := by
  classical
  exact fun v => decide (v.1 ∈ bac_rightComplement omega n)


theorem crr_boxRColour_sidesConnected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
    Ising.kwg_ColourSidesConnected (crr_boxPlanar n).G (crr_boxRColour omega n) := by
  classical
  intro b x y
  cases b with
  | false =>
      have hxNotR : x.1.1 ∉ bac_rightComplement omega n := by
        simpa [crr_boxRColour] using x.2
      have hyNotR : y.1.1 ∉ bac_rightComplement omega n := by
        simpa [crr_boxRColour] using y.2
      have hxFill : x.1.1 ∈ crr_leftFill omega n := ⟨x.1.2, hxNotR⟩
      have hyFill : y.1.1 ∈ crr_leftFill omega n := ⟨y.1.2, hyNotR⟩
      have hxy := crr_leftFill_connected_pair omega n hxFill hyFill
      let phi : ((hypercubicLattice 2).induce (crr_leftFill omega n)) →g
          ((crr_boxPlanar n).G.induce {v | crr_boxRColour omega n v = false}) := {
        toFun := fun (z : crr_leftFill omega n) =>
          (⟨(⟨z.1, z.2.1⟩ : (crr_boxPlanar n).V),
            by simp [crr_boxRColour, z.2.2]⟩ :
            {v : (crr_boxPlanar n).V // crr_boxRColour omega n v = false})
        map_rel' := by
          intro a b hab
          exact hab }
      have hm := hxy.map phi
      convert hm using 1 <;> rfl
  | true =>
      have hxR : x.1.1 ∈ bac_rightComplement omega n := by
        simpa [crr_boxRColour] using x.2
      have hyR : y.1.1 ∈ bac_rightComplement omega n := by
        simpa [crr_boxRColour] using y.2
      have hxy := crr_rightComplement_connected_induced omega n hnoH hxR hyR
      let phi : ((hypercubicLattice 2).induce (bac_rightComplement omega n)) →g
          ((crr_boxPlanar n).G.induce {v | crr_boxRColour omega n v = true}) := {
        toFun := fun (z : bac_rightComplement omega n) =>
          (⟨(⟨z.1, (bac_rightComplement_mem omega n z.2).1⟩ :
              (crr_boxPlanar n).V), by simp [crr_boxRColour, z.2]⟩ :
            {v : (crr_boxPlanar n).V // crr_boxRColour omega n v = true})
        map_rel' := by
          intro a b hab
          exact hab }
      have hm := hxy.map phi
      convert hm using 1 <;> rfl


theorem crr_boxR_dualEven_subset_eq
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n)
    (F : Finset (Ising.kwg_Edge (crr_boxPlanar n)))
    (hsub : F ⊆ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
      (crr_boxRColour omega n))
    (hne : F.Nonempty)
    (heven : Ising.kwg_IsEven (Ising.kwg_dualEnds (crr_boxPlanar n)) F) :
    F = Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
      (crr_boxRColour omega n) :=
  Ising.kwg_dualEven_subset_bond_eq (crr_boxPlanar n) (crr_boxRColour omega n)
    (crr_boxRColour_sidesConnected omega n hnoH) F hsub hne heven



def crr_LRFaceGraph (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    SimpleGraph (Site 2) where
  Adj f g := (faceBoundaryGraph (bac_rightComplement omega n)).Adj f g ∧
    crc2_IsBoxInteriorEdge n f g
  symm := by
    rintro f g ⟨hfg, p, q, hpq, hp, hq⟩
    refine ⟨hfg.symm, p, q, ?_, hp, hq⟩
    calc
      sharedPrimalEdge g f = sharedPrimalEdge f g := sharedPrimalEdge_comm_of_adj hfg.1.symm
      _ = s(p, q) := hpq
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1.1⟩

noncomputable instance crr_LRFaceGraph_locallyFinite
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    SimpleGraph.LocallyFinite (crr_LRFaceGraph omega n) := fun f => by
  let toLat : (crr_LRFaceGraph omega n).neighborSet f →
      (hypercubicLattice 2).neighborSet f := fun z => ⟨z.1, z.2.1.1⟩
  exact Fintype.ofInjective toLat (fun _ _ h => Subtype.ext
    (congrArg (fun z : (hypercubicLattice 2).neighborSet f => (z : Site 2)) h))


theorem crr_faceAdj_isBoxInterior_of_mem_interior {n : Int} {f g : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1))
    (hfg : (hypercubicLattice 2).Adj f g) : crc2_IsBoxInteriorEdge n f g := by
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by
    funext i
    fin_cases i <;> simp [a, b]
  have hab := mem_rect.mp hf
  rw [hfeq] at hfg
  rcases crr_face_nbr_cases a b g hfg with rfl | rfl | rfl | rfl
  · refine ⟨![a + 1, b], ![a + 1, b + 1], ?_, ?_, ?_⟩
    · rw [hfeq, sharedPrimalEdge_right]
      unfold faceCorner10 faceCorner11
      rfl
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![a, b], ![a, b + 1], ?_, ?_, ?_⟩
    · rw [hfeq, sharedPrimalEdge_left]
      unfold faceCorner00 faceCorner01
      rfl
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![a, b + 1], ![a + 1, b + 1], ?_, ?_, ?_⟩
    · rw [hfeq, sharedPrimalEdge_top]
      unfold faceCorner01 faceCorner11
      rfl
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![a, b], ![a + 1, b], ?_, ?_, ?_⟩
    · rw [hfeq, sharedPrimalEdge_bottom]
      unfold faceCorner00 faceCorner10
      rfl
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega


theorem crr_LRFaceGraph_degree_eq_faceBoundary_degree
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
    (crr_LRFaceGraph omega n).degree f =
      (faceBoundaryGraph (bac_rightComplement omega n)).degree f := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply congrArg Finset.card
  ext g
  simp only [SimpleGraph.mem_neighborFinset]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, crr_faceAdj_isBoxInterior_of_mem_interior hf h.1⟩


theorem crr_LRFaceGraph_degree_even_of_interior
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
    Even ((crr_LRFaceGraph omega n).degree f) := by
  rw [crr_LRFaceGraph_degree_eq_faceBoundary_degree omega n hf]
  exact degree_faceBoundaryGraph_even (bac_rightComplement omega n) f



theorem crr_LRFaceGraph_adj_of_shared
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hpL : p ∈ bcd_leftReach omega n)
    (hqR : q ∈ bac_rightComplement omega n)
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    (crr_LRFaceGraph omega n).Adj f g := by
  refine ⟨⟨hfg, ?_⟩, p, q, hshared, hpbox, hqbox⟩
  rw [hshared, bdEdge_mk]
  have hpR : p ∉ bac_rightComplement omega n := fun hpR =>
    (bac_rightComplement_mem omega n hpR).2 hpL
  simp [hpR, hqR]


theorem crr_interfaceSideWith_LRNeighbor
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f q : Site 2}
    (h : crr_InterfaceSideWith omega n f q) :
    ∃ g : Site 2, (crr_LRFaceGraph omega n).Adj f g := by
  obtain ⟨hqR, pL, hpL, hadj, hpLbox, hqbox, hpLc, hqc⟩ := h
  set a := f 0 with ha
  set b := f 1 with hb
  have hfe : f = ![a, b] := by funext i; fin_cases i <;> simp [ha, hb]
  rcases hpLc with rfl | rfl | rfl | rfl <;> rcases hqc with rfl | rfl | rfl | rfl <;>
    solve
      | (exfalso; revert hadj; rw [hypercubicLattice_adj, Fin.sum_univ_two];
         simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
      | (rw [hfe]; refine ⟨![a, b - 1], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_bottom,
            faceCorner00, faceCorner10])
      | (rw [hfe]; refine ⟨![a, b - 1], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_bottom,
            faceCorner00, faceCorner10, Sym2.eq_swap])
      | (rw [hfe]; refine ⟨![a, b + 1], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_top,
            faceCorner01, faceCorner11])
      | (rw [hfe]; refine ⟨![a, b + 1], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_top,
            faceCorner01, faceCorner11, Sym2.eq_swap])
      | (rw [hfe]; refine ⟨![a - 1, b], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_left,
            faceCorner00, faceCorner01])
      | (rw [hfe]; refine ⟨![a - 1, b], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_left,
            faceCorner00, faceCorner01, Sym2.eq_swap])
      | (rw [hfe]; refine ⟨![a + 1, b], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_right,
            faceCorner10, faceCorner11])
      | (rw [hfe]; refine ⟨![a + 1, b], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_right,
            faceCorner10, faceCorner11, Sym2.eq_swap])



theorem crr_cutEdge_flanks_LRAdj
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (e : Ising.kwg_Edge (crr_boxPlanar n))
    (he : e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
      (crr_boxRColour omega n)) :
    (crr_LRFaceGraph omega n).Adj
      (Ising.kwg_flankLeft (crr_boxPlanar n) e)
      (Ising.kwg_flankRight (crr_boxPlanar n) e) := by
  classical
  rcases e with ⟨e, hedge⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : (crr_boxPlanar n).G.Adj x y :=
        (SimpleGraph.mem_edgeSet (crr_boxPlanar n).G).mp hedge
      have hxyLat : (hypercubicLattice 2).Adj (x : Site 2) (y : Site 2) := hxy
      have hsplit : crr_boxRColour omega n x ≠ crr_boxRColour omega n y := by
        simpa [Ising.kwg_primalEnds] using
          (Ising.kwg_mem_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
            (crr_boxRColour omega n) ⟨s(x, y), hedge⟩).mp he
      have hshared : sharedPrimalEdge
          (Ising.kwg_flankLeft (crr_boxPlanar n) ⟨s(x, y), hedge⟩)
          (Ising.kwg_flankRight (crr_boxPlanar n) ⟨s(x, y), hedge⟩) =
          s((x : Site 2), (y : Site 2)) := by
        simpa [Ising.kwg_embeddedEdge, Sym2.map_mk] using
          Ising.kwg_flanks_shared (crr_boxPlanar n) ⟨s(x, y), hedge⟩
      have hflank := Ising.kwg_flanks_adj (crr_boxPlanar n) ⟨s(x, y), hedge⟩
      by_cases hxR : (x : Site 2) ∈ bac_rightComplement omega n
      · have hyNotR : (y : Site 2) ∉ bac_rightComplement omega n := by
          intro hyR
          apply hsplit
          simp [crr_boxRColour, hxR, hyR]
        have hyL : (y : Site 2) ∈ bcd_leftReach omega n := by
          rcases crr_nbr_of_rCorner omega n hxR hxyLat y.2 with hyL | hyR
          · exact hyL
          · exact absurd hyR hyNotR
        exact crr_LRFaceGraph_adj_of_shared omega n hflank
          (hshared.trans Sym2.eq_swap) hyL hxR y.2 x.2
      · have hyR : (y : Site 2) ∈ bac_rightComplement omega n := by
          by_contra hyNotR
          apply hsplit
          simp [crr_boxRColour, hxR, hyNotR]
        have hxL : (x : Site 2) ∈ bcd_leftReach omega n := by
          rcases crr_nbr_of_rCorner omega n hyR hxyLat.symm x.2 with hxL | hxR'
          · exact hxL
          · exact absurd hxR' hxR
        exact crr_LRFaceGraph_adj_of_shared omega n hflank hshared hxL hyR x.2 y.2


noncomputable def crr_LRComponentEdges
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) (f : Site 2) :
    Finset (Ising.kwg_Edge (crr_boxPlanar n)) := by
  classical
  exact (Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
    (crr_boxRColour omega n)).filter fun e =>
      (crr_LRFaceGraph omega n).Reachable f
        (Ising.kwg_flankLeft (crr_boxPlanar n) e)

theorem crr_mem_LRComponentEdges_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) (f : Site 2)
    (e : Ising.kwg_Edge (crr_boxPlanar n)) :
    e ∈ crr_LRComponentEdges omega n f ↔
      e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
        (crr_boxRColour omega n) ∧
      (crr_LRFaceGraph omega n).Reachable f
        (Ising.kwg_flankLeft (crr_boxPlanar n) e) := by
  classical
  simp [crr_LRComponentEdges]


theorem crr_boxImage_edge_endpoint_mem {n : Int} {e : Sym2 (Site 2)}
    (he : e ∈ (imageGraph (crr_boxPlanar n)).edgeSet) {z : Site 2} (hz : z ∈ e) :
    z ∈ rect 0 n 0 n := by
  induction e using Sym2.inductionOn with
  | _ p q =>
      have hpq : (imageGraph (crr_boxPlanar n)).Adj p q :=
        (SimpleGraph.mem_edgeSet (imageGraph (crr_boxPlanar n))).mp he
      rw [imageGraph_adj] at hpq
      obtain ⟨x, y, _hxy, hxp, hyq⟩ := hpq
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · rw [← hxp]
        exact x.2
      · rw [← hyq]
        exact y.2



theorem crr_face_interior_or_frame {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (h : crc2_IsBoxInteriorEdge n f g) :
    f ∈ rect 0 (n - 1) 0 (n - 1) ∨
      f 0 = -1 ∨ f 0 = n ∨ f 1 = -1 ∨ f 1 = n := by
  obtain ⟨p, q, hpq, hp, hq⟩ := h
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  have endpoints : ∀ u v : Site 2, sharedPrimalEdge f g = s(u, v) →
      u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
    intro u v huv
    rw [huv] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp, hq⟩
    · exact ⟨hq, hp⟩
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · have he := endpoints (faceCorner10 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_right])
    rw [hfeq, mem_rect] at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner10, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner01 a b) (by
      rw [hfeq, sharedPrimalEdge_left])
    rw [hfeq, mem_rect] at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner01, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner01 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_top])
    rw [hfeq, mem_rect] at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner01, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner10 a b) (by
      rw [hfeq, sharedPrimalEdge_bottom])
    rw [hfeq, mem_rect] at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner10, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega


theorem crr_boxEdge_one_flank_interior {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (h : crc2_IsBoxInteriorEdge n f g) :
    f ∈ rect 0 (n - 1) 0 (n - 1) ∨ g ∈ rect 0 (n - 1) 0 (n - 1) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := h
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  have endpoints : ∀ u v : Site 2, sharedPrimalEdge f g = s(u, v) →
      u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
    intro u v huv
    rw [huv] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp, hq⟩
    · exact ⟨hq, hp⟩
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · have he := endpoints (faceCorner10 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_right])
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner10, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner01 a b) (by
      rw [hfeq, sharedPrimalEdge_left])
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner01, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner01 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_top])
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner01, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner10 a b) (by
      rw [hfeq, sharedPrimalEdge_bottom])
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner10, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega

theorem crr_whb_box_adj_leftLine {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (hf : f 0 = -1) (hg : g 0 = -1) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  refine ⟨hfg, ?_⟩
  intro he
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · simp only [Matrix.cons_val_zero] at hf hg; omega
  · simp only [Matrix.cons_val_zero] at hf hg; omega
  · rw [hfeq, sharedPrimalEdge_top] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_left (faceCorner01 a b) (faceCorner11 a b))
    rw [mem_rect] at hz
    simp only [faceCorner01, Matrix.cons_val_zero] at hz
    omega
  · rw [hfeq, sharedPrimalEdge_bottom] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_left (faceCorner00 a b) (faceCorner10 a b))
    rw [mem_rect] at hz
    simp only [faceCorner00, Matrix.cons_val_zero] at hz
    omega

theorem crr_whb_box_adj_rightLine {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (hf : f 0 = n) (hg : g 0 = n) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  refine ⟨hfg, ?_⟩
  intro he
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · simp only [Matrix.cons_val_zero] at hf hg; omega
  · simp only [Matrix.cons_val_zero] at hf hg; omega
  · rw [hfeq, sharedPrimalEdge_top] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_right (faceCorner01 a b) (faceCorner11 a b))
    rw [mem_rect] at hz
    simp only [faceCorner11, Matrix.cons_val_zero] at hz
    omega
  · rw [hfeq, sharedPrimalEdge_bottom] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_right (faceCorner00 a b) (faceCorner10 a b))
    rw [mem_rect] at hz
    simp only [faceCorner10, Matrix.cons_val_zero] at hz
    omega

theorem crr_whb_box_adj_bottomLine {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (hf : f 1 = -1) (hg : g 1 = -1) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  refine ⟨hfg, ?_⟩
  intro he
  let a := f 0
  let b := f 1
  have hbline : b = -1 := by simpa [b] using hf
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · rw [hfeq, sharedPrimalEdge_right] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_left (faceCorner10 a b) (faceCorner11 a b))
    rw [mem_rect] at hz
    simp only [faceCorner10, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    omega
  · rw [hfeq, sharedPrimalEdge_left] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_left (faceCorner00 a b) (faceCorner01 a b))
    rw [mem_rect] at hz
    simp only [faceCorner00, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    omega
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hg; omega
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hg; omega

theorem crr_whb_box_adj_topLine {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (hf : f 1 = n) (hg : g 1 = n) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  refine ⟨hfg, ?_⟩
  intro he
  let a := f 0
  let b := f 1
  have hbline : b = n := by simpa [b] using hf
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · rw [hfeq, sharedPrimalEdge_right] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_right (faceCorner10 a b) (faceCorner11 a b))
    rw [mem_rect] at hz
    simp only [faceCorner11, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    omega
  · rw [hfeq, sharedPrimalEdge_left] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_right (faceCorner00 a b) (faceCorner01 a b))
    rw [mem_rect] at hz
    simp only [faceCorner01, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    omega
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hg; omega
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hg; omega


theorem crr_frame_reachable_outerBeacon (n : Int) {f : Site 2}
    (hf : f 0 = -1 ∨ f 0 = n ∨ f 1 = -1 ∨ f 1 = n) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Reachable f ![-1, -1] := by
  classical
  let H := whb_faceRegion (imageGraph (crr_boxPlanar n))
  have leftRun : ∀ y0 y1 : Int, H.Reachable (![-1, y0] : Site 2) ![-1, y1] := by
    intro y0 y1
    let p := sw_vertSeg (-1) y0 y1
    refine ⟨p.transfer H ?_⟩
    intro e he
    induction e with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hu := (sw_vertSeg (-1) y0 y1).fst_mem_support_of_mem_edges he
      have hv := (sw_vertSeg (-1) y0 y1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, _htu, rfl⟩ := (sw_vertSeg_mem_support (-1) y0 y1 u).mp hu
      obtain ⟨tv, _htv, rfl⟩ := (sw_vertSeg_mem_support (-1) y0 y1 v).mp hv
      exact crr_whb_box_adj_leftLine
        ((sw_vertSeg (-1) y0 y1).adj_of_mem_edges he) (by simp) (by simp)
  have rightRun : ∀ y0 y1 : Int, H.Reachable (![n, y0] : Site 2) ![n, y1] := by
    intro y0 y1
    let p := sw_vertSeg n y0 y1
    refine ⟨p.transfer H ?_⟩
    intro e he
    induction e with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hu := (sw_vertSeg n y0 y1).fst_mem_support_of_mem_edges he
      have hv := (sw_vertSeg n y0 y1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, _htu, rfl⟩ := (sw_vertSeg_mem_support n y0 y1 u).mp hu
      obtain ⟨tv, _htv, rfl⟩ := (sw_vertSeg_mem_support n y0 y1 v).mp hv
      exact crr_whb_box_adj_rightLine
        ((sw_vertSeg n y0 y1).adj_of_mem_edges he) (by simp) (by simp)
  have bottomRun : ∀ x0 x1 : Int, H.Reachable (![x0, -1] : Site 2) ![x1, -1] := by
    intro x0 x1
    let p := sw_horizSeg (-1) x0 x1
    refine ⟨p.transfer H ?_⟩
    intro e he
    induction e with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hu := (sw_horizSeg (-1) x0 x1).fst_mem_support_of_mem_edges he
      have hv := (sw_horizSeg (-1) x0 x1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, _htu, rfl⟩ := (sw_horizSeg_mem_support (-1) x0 x1 u).mp hu
      obtain ⟨tv, _htv, rfl⟩ := (sw_horizSeg_mem_support (-1) x0 x1 v).mp hv
      exact crr_whb_box_adj_bottomLine
        ((sw_horizSeg (-1) x0 x1).adj_of_mem_edges he) (by simp) (by simp)
  have topRun : ∀ x0 x1 : Int, H.Reachable (![x0, n] : Site 2) ![x1, n] := by
    intro x0 x1
    let p := sw_horizSeg n x0 x1
    refine ⟨p.transfer H ?_⟩
    intro e he
    induction e with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hu := (sw_horizSeg n x0 x1).fst_mem_support_of_mem_edges he
      have hv := (sw_horizSeg n x0 x1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, _htu, rfl⟩ := (sw_horizSeg_mem_support n x0 x1 u).mp hu
      obtain ⟨tv, _htv, rfl⟩ := (sw_horizSeg_mem_support n x0 x1 v).mp hv
      exact crr_whb_box_adj_topLine
        ((sw_horizSeg n x0 x1).adj_of_mem_edges he) (by simp) (by simp)
  rcases hf with hf | hf | hf | hf
  · have hfeq : f = ![-1, f 1] := by funext i; fin_cases i <;> simp [hf]
    rw [hfeq]
    exact leftRun _ _
  · have hfeq : f = ![n, f 1] := by funext i; fin_cases i <;> simp [hf]
    rw [hfeq]
    exact (rightRun _ _).trans (bottomRun _ _)
  · have hfeq : f = ![f 0, -1] := by funext i; fin_cases i <;> simp [hf]
    rw [hfeq]
    exact bottomRun _ _
  · have hfeq : f = ![f 0, n] := by funext i; fin_cases i <;> simp [hf]
    rw [hfeq]
    exact (topRun _ _).trans (leftRun _ _)


theorem crr_sharedEdge_mem_boxImage {n : Int} {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hp : p ∈ rect 0 n 0 n) (hq : q ∈ rect 0 n 0 n) :
    sharedPrimalEdge f g ∈ (imageGraph (crr_boxPlanar n)).edgeSet := by
  obtain ⟨p', q', hpq', hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg
  rw [hpq'] at hshared ⊢
  rw [Sym2.eq_iff] at hshared
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  rcases hshared with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨p', hp⟩, ⟨q', hq⟩, hpqAdj, rfl, rfl⟩
  · exact ⟨⟨p', hq⟩, ⟨q', hp⟩, hpqAdj, rfl, rfl⟩


theorem crr_whb_box_interior_isolated {n : Int} {f g : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
    ¬ (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  rintro ⟨hfg, hnot⟩
  obtain ⟨p, q, hpq, hp, hq⟩ := crr_faceAdj_isBoxInterior_of_mem_interior hf hfg
  exact hnot (crr_sharedEdge_mem_boxImage hfg hpq hp hq)


theorem crr_whb_box_component_singleton {n : Int} {f g : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1))
    (hcomp : (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f =
      (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk g) :
    f = g := by
  have hreach := ConnectedComponent.exact hcomp
  obtain ⟨w⟩ := hreach
  cases w with
  | nil => rfl
  | cons hadj _ => exact (crr_whb_box_interior_isolated hf hadj).elim



theorem crr_nonOuter_flank_interior {n : Int}
    (e : Ising.kwg_Edge (crr_boxPlanar n)) {f : Site 2}
    (hf : f = Ising.kwg_flankLeft (crr_boxPlanar n) e ∨
      f = Ising.kwg_flankRight (crr_boxPlanar n) e)
    (houter : (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f ≠
      (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk ![-1, -1]) :
    f ∈ rect 0 (n - 1) 0 (n - 1) := by
  have hfg := Ising.kwg_flanks_adj (crr_boxPlanar n) e
  have hint : crc2_IsBoxInteriorEdge n
      (Ising.kwg_flankLeft (crr_boxPlanar n) e)
      (Ising.kwg_flankRight (crr_boxPlanar n) e) := by
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      refine ⟨x.1, y.1, ?_, x.2, y.2⟩
      simpa [Ising.kwg_embeddedEdge, Sym2.map_mk] using
        Ising.kwg_flanks_shared (crr_boxPlanar n) ⟨s(x, y), he⟩
  rcases hf with rfl | rfl
  · rcases crr_face_interior_or_frame hfg hint with hin | hframe
    · exact hin
    · exact (houter (ConnectedComponent.sound
        (crr_frame_reachable_outerBeacon n hframe))).elim
  · have hint' : crc2_IsBoxInteriorEdge n
        (Ising.kwg_flankRight (crr_boxPlanar n) e)
        (Ising.kwg_flankLeft (crr_boxPlanar n) e) := by
      obtain ⟨p, q, hpq, hp, hq⟩ := hint
      refine ⟨p, q, ?_, hp, hq⟩
      calc
        sharedPrimalEdge (Ising.kwg_flankRight (crr_boxPlanar n) e)
            (Ising.kwg_flankLeft (crr_boxPlanar n) e) =
            sharedPrimalEdge (Ising.kwg_flankLeft (crr_boxPlanar n) e)
              (Ising.kwg_flankRight (crr_boxPlanar n) e) :=
          sharedPrimalEdge_comm_of_adj hfg.symm
        _ = s(p, q) := hpq
    rcases crr_face_interior_or_frame hfg.symm hint' with hin | hframe
    · exact hin
    · exact (houter (ConnectedComponent.sound
        (crr_frame_reachable_outerBeacon n hframe))).elim



theorem crr_LRAdj_exists_cutEdge_incident
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f g : Site 2}
    (hfint : f ∈ rect 0 (n - 1) 0 (n - 1))
    (hfg : (crr_LRFaceGraph omega n).Adj f g) :
    ∃ e : Ising.kwg_Edge (crr_boxPlanar n),
      e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
        (crr_boxRColour omega n) ∧
      Ising.kwg_incidentMod2
        ((whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f)
        (Ising.kwg_dualEnds (crr_boxPlanar n) e) := by
  classical
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1.1
  obtain ⟨u, v, huv, hu, hv⟩ := hfg.2
  rw [hpq] at huv
  rw [Sym2.eq_iff] at huv
  have hp : p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n := by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hu, hv⟩
    · exact ⟨hv, hu⟩
  let x : (crr_boxPlanar n).V := ⟨p, hp.1⟩
  let y : (crr_boxPlanar n).V := ⟨q, hp.2⟩
  have hxy : (crr_boxPlanar n).G.Adj x y := hpqAdj
  let e : Ising.kwg_Edge (crr_boxPlanar n) :=
    ⟨s(x, y), (SimpleGraph.mem_edgeSet _).2 hxy⟩
  have hecut : e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
      (crr_boxRColour omega n) := by
    rw [Ising.kwg_mem_cutSet]
    change crr_boxRColour omega n x ≠ crr_boxRColour omega n y
    have hbd := hfg.1.2
    rw [hpq, bdEdge_mk] at hbd
    by_cases hpR : p ∈ bac_rightComplement omega n <;>
      by_cases hqR : q ∈ bac_rightComplement omega n <;>
      simp_all [crr_boxRColour, x, y]
  refine ⟨e, hecut, ?_⟩
  have hshared : sharedPrimalEdge
      (Ising.kwg_flankLeft (crr_boxPlanar n) e)
      (Ising.kwg_flankRight (crr_boxPlanar n) e) = sharedPrimalEdge f g := by
    rw [Ising.kwg_flanks_shared, hpq]
    simp [e, x, y, Ising.kwg_embeddedEdge, Sym2.map_mk]
  have hpairs : s(Ising.kwg_flankLeft (crr_boxPlanar n) e,
      Ising.kwg_flankRight (crr_boxPlanar n) e) = s(f, g) :=
    (jce_sharedPrimalEdge_inj (Ising.kwg_flanks_adj (crr_boxPlanar n) e) hfg.1.1).mpr hshared
  rw [Sym2.eq_iff] at hpairs
  have hcomp_ne :
      (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f ≠
      (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk g := by
    intro heq
    have := crr_whb_box_component_singleton hfint heq
    exact (hypercubicLattice 2).irrefl (this ▸ hfg.1.1)
  rcases hpairs with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · unfold Ising.kwg_dualEnds
    rw [hL, hR]
    exact (Ising.kwg_incidentMod2_mk _ _ _).2 (Or.inl ⟨rfl, hcomp_ne.symm⟩)
  · unfold Ising.kwg_dualEnds
    rw [hL, hR]
    exact (Ising.kwg_incidentMod2_mk _ _ _).2 (Or.inr ⟨rfl, hcomp_ne.symm⟩)

theorem crr_LRAdj_has_interior_endpoint {omega : ConfigSpace (Sym2 (Site 2))} {n : Int}
    {f g : Site 2} (hfg : (crr_LRFaceGraph omega n).Adj f g) :
    f ∈ rect 0 (n - 1) 0 (n - 1) ∨ g ∈ rect 0 (n - 1) 0 (n - 1) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := hfg.2
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  have endpoints : ∀ u v : Site 2, sharedPrimalEdge f g = s(u, v) →
      u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
    intro u v huv
    rw [huv] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp, hq⟩
    · exact ⟨hq, hp⟩
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg.1.1) with rfl | rfl | rfl | rfl
  · have he := endpoints (faceCorner10 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_right])
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner10, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner01 a b) (by
      rw [hfeq, sharedPrimalEdge_left])
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner01, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · have he := endpoints (faceCorner01 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_top])
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner01, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner10 a b) (by
      rw [hfeq, sharedPrimalEdge_bottom])
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner10, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega


noncomputable def crr_boxRCut
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    Finset (Ising.kwg_Edge (crr_boxPlanar n)) :=
  Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n)) (crr_boxRColour omega n)


noncomputable def crr_boxFaceRep (n : Int) (C : Ising.kwg_Face (crr_boxPlanar n)) : Site 2 :=
  C.nonempty_supp.some

theorem crr_boxFaceRep_component (n : Int) (C : Ising.kwg_Face (crr_boxPlanar n)) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk
      (crr_boxFaceRep n C) = C :=
  (ConnectedComponent.mem_supp_iff C _).mp C.nonempty_supp.some_mem



noncomputable def crr_cutFaceHom
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    Ising.kwg_deleteVertexGraph
        (Ising.kwg_faceSupportGraph
          (fun e : ↑(crr_boxRCut omega n) =>
            Ising.kwg_dualEnds (crr_boxPlanar n) e.1))
        ((whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk ![-1, -1]) →g
      crr_LRFaceGraph omega n where
  toFun C := crr_boxFaceRep n C
  map_rel' := by
    intro C D hCD
    obtain ⟨hCDsupp, hCout, hDout⟩ := hCD
    obtain ⟨hCDne, e, heEnds⟩ := hCDsupp
    have hecut : e.1 ∈ crr_boxRCut omega n := e.2
    have hflank : (crr_LRFaceGraph omega n).Adj
        (Ising.kwg_flankLeft (crr_boxPlanar n) e.1)
        (Ising.kwg_flankRight (crr_boxPlanar n) e.1) := by
      apply crr_cutEdge_flanks_LRAdj omega n e.1
      exact hecut
    have hflInt : Ising.kwg_flankLeft (crr_boxPlanar n) e.1 ∈
        rect 0 (n - 1) 0 (n - 1) := by
      apply crr_nonOuter_flank_interior e.1 (Or.inl rfl)
      intro hout
      unfold Ising.kwg_dualEnds at heEnds
      rw [Sym2.eq_iff] at heEnds
      rcases heEnds with ⟨hLC, _⟩ | ⟨hLD, _⟩
      · exact hCout (hLC.symm.trans hout)
      · exact hDout (hLD.symm.trans hout)
    have hfrInt : Ising.kwg_flankRight (crr_boxPlanar n) e.1 ∈
        rect 0 (n - 1) 0 (n - 1) := by
      apply crr_nonOuter_flank_interior e.1 (Or.inr rfl)
      intro hout
      unfold Ising.kwg_dualEnds at heEnds
      rw [Sym2.eq_iff] at heEnds
      rcases heEnds with ⟨_, hRD⟩ | ⟨_, hRC⟩
      · exact hDout (hRD.symm.trans hout)
      · exact hCout (hRC.symm.trans hout)
    unfold Ising.kwg_dualEnds at heEnds
    rw [Sym2.eq_iff] at heEnds
    rcases heEnds with ⟨hLC, hRD⟩ | ⟨hLD, hRC⟩
    · have hrepL : crr_boxFaceRep n C = Ising.kwg_flankLeft (crr_boxPlanar n) e.1 := by
        symm
        apply crr_whb_box_component_singleton hflInt
        rw [crr_boxFaceRep_component, hLC]
      have hrepR : crr_boxFaceRep n D = Ising.kwg_flankRight (crr_boxPlanar n) e.1 := by
        symm
        apply crr_whb_box_component_singleton hfrInt
        rw [crr_boxFaceRep_component, hRD]
      simpa [hrepL, hrepR] using hflank
    · have hrepL : crr_boxFaceRep n D = Ising.kwg_flankLeft (crr_boxPlanar n) e.1 := by
        symm
        apply crr_whb_box_component_singleton hflInt
        rw [crr_boxFaceRep_component, hLD]
      have hrepR : crr_boxFaceRep n C = Ising.kwg_flankRight (crr_boxPlanar n) e.1 := by
        symm
        apply crr_whb_box_component_singleton hfrInt
        rw [crr_boxFaceRep_component, hRC]
      simpa [hrepL, hrepR] using hflank.symm


theorem crr_interfaceSide_reaches_interior
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f q : Site 2}
    (h : crr_InterfaceSideWith omega n f q) :
    ∃ f' : Site 2, f' ∈ rect 0 (n - 1) 0 (n - 1) ∧
      (crr_LRFaceGraph omega n).Reachable f f' ∧
      ∃ g, (crr_LRFaceGraph omega n).Adj f' g := by
  obtain ⟨g, hfg⟩ := crr_interfaceSideWith_LRNeighbor omega n h
  rcases crr_LRAdj_has_interior_endpoint hfg with hf | hg
  · exact ⟨f, hf, SimpleGraph.Reachable.refl _, g, hfg⟩
  · exact ⟨g, hg, hfg.reachable, f, hfg.symm⟩


theorem crr_interior_LRFaceGraph_reachable
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n)
    {f₁ f₂ : Site 2}
    (hf₁ : f₁ ∈ rect 0 (n - 1) 0 (n - 1))
    (hf₂ : f₂ ∈ rect 0 (n - 1) 0 (n - 1))
    (hinc₁ : ∃ g, (crr_LRFaceGraph omega n).Adj f₁ g)
    (hinc₂ : ∃ g, (crr_LRFaceGraph omega n).Adj f₂ g) :
    (crr_LRFaceGraph omega n).Reachable f₁ f₂ := by
  classical
  let P := crr_boxPlanar n
  let B := crr_boxRCut omega n
  let Rg := whb_faceRegion (imageGraph P)
  let O : Ising.kwg_Face P := Rg.connectedComponentMk ![-1, -1]
  let C₁ : Ising.kwg_Face P := Rg.connectedComponentMk f₁
  let C₂ : Ising.kwg_Face P := Rg.connectedComponentMk f₂
  obtain ⟨g₁, hfg₁⟩ := hinc₁
  obtain ⟨g₂, hfg₂⟩ := hinc₂
  obtain ⟨e₁, he₁B, he₁inc⟩ := crr_LRAdj_exists_cutEdge_incident omega n hf₁ hfg₁
  obtain ⟨e₂, he₂B, he₂inc⟩ := crr_LRAdj_exists_cutEdge_incident omega n hf₂ hfg₂
  have hBne : B.Nonempty := ⟨e₁, he₁B⟩
  have hBeven : Ising.kwg_IsEven (Ising.kwg_dualEnds P) B := by
    exact Ising.kwg_primalCut_isEven P (crr_boxRColour omega n)
  have hBmin : ∀ S : Finset (Ising.kwg_Edge P), S ⊆ B → S.Nonempty →
      Ising.kwg_IsEven (Ising.kwg_dualEnds P) S → S = B := by
    intro S hsub hne heven
    exact crr_boxR_dualEven_subset_eq omega n hnoH S hsub hne heven
  have hC₁out : C₁ ≠ O := by
    intro heq
    have hface := crr_whb_box_component_singleton hf₁ heq
    have hc := congrFun hface 0
    rw [mem_rect] at hf₁
    simp at hc
    omega
  have hC₂out : C₂ ≠ O := by
    intro heq
    have hface := crr_whb_box_component_singleton hf₂ heq
    have hc := congrFun hface 0
    rw [mem_rect] at hf₂
    simp at hc
    omega
  have hdual := Ising.kwg_minimalEvenFinset_nonOuter_reachable
    (Ising.kwg_dualEnds P) B O hBne hBeven hBmin hC₁out hC₂out
    ⟨e₁, he₁B, he₁inc⟩ ⟨e₂, he₂B, he₂inc⟩
  have hmapped := hdual.map (crr_cutFaceHom omega n)
  have hrep₁ : crr_boxFaceRep n C₁ = f₁ := by
    symm
    apply crr_whb_box_component_singleton hf₁
    exact (crr_boxFaceRep_component n C₁).symm
  have hrep₂ : crr_boxFaceRep n C₂ = f₂ := by
    symm
    apply crr_whb_box_component_singleton hf₂
    exact (crr_boxFaceRep_component n C₂).symm
  simpa [crr_cutFaceHom, P, B, Rg, O, C₁, C₂, hrep₁, hrep₂] using hmapped


theorem crr_leftFill_finite (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (crr_leftFill ω n).Finite :=
  (rect_finite 0 n 0 n).subset diff_subset






theorem crr_leftFill_bdEdge_is_leftReach_bdEdge
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q)
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n)
    (hbd : bdEdge (crr_leftFill ω n) s(p, q)) :
    bdEdge (bcd_leftReach ω n) s(p, q) := by
  rw [bdEdge_mk] at hbd ⊢
  by_cases hpR : p ∈ bac_rightComplement ω n
  · have hpFill : p ∉ crr_leftFill ω n := by simp [crr_leftFill, hpR]
    have hqFill : q ∈ crr_leftFill ω n := by
      by_contra hq
      exact hpFill (hbd.mpr hq)
    have hqR : q ∉ bac_rightComplement ω n := hqFill.2
    have hqL : q ∈ bcd_leftReach ω n := by
      rcases crr_nbr_of_rCorner ω n hpR hadj hqbox with hqL | hqR'
      · exact hqL
      · exact absurd hqR' hqR
    have hpL : p ∉ bcd_leftReach ω n := (bac_rightComplement_mem ω n hpR).2
    simp [hpL, hqL]
  · have hpFill : p ∈ crr_leftFill ω n := ⟨hpbox, hpR⟩
    have hqNotFill : q ∉ crr_leftFill ω n := hbd.mp hpFill
    have hqR : q ∈ bac_rightComplement ω n := by
      by_contra hqR
      exact hqNotFill ⟨hqbox, hqR⟩
    have hpL : p ∈ bcd_leftReach ω n := by
      rcases crr_nbr_of_rCorner ω n hqR hadj.symm hpbox with hpL | hpR'
      · exact hpL
      · exact absurd hpR' hpR
    have hqL : q ∉ bcd_leftReach ω n := (bac_rightComplement_mem ω n hqR).2
    simp [hpL, hqL]



theorem crr_leftFill_faceBoundary_inBox_pmd
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f g p q : Site 2}
    (hfg : (faceBoundaryGraph (crr_leftFill ω n)).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    (pmd_boxFaceBarrier ω n).Adj f g := by
  refine ⟨hfg.1, p, q, hshared, ?_, hpbox, hqbox⟩
  obtain ⟨p', q', hpq', hadj'⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  rw [hpq'] at hshared
  rw [Sym2.eq_iff] at hshared
  rcases hshared with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply crr_leftFill_bdEdge_is_leftReach_bdEdge ω n hadj' hpbox hqbox
    rw [← hpq']
    exact hfg.2
  · apply crr_leftFill_bdEdge_is_leftReach_bdEdge ω n hadj'.symm hpbox hqbox
    rw [Sym2.eq_swap, ← hpq']
    exact hfg.2


theorem crr_LRFaceGraph_adj_leftFill
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f g : Site 2}
    (h : (crr_LRFaceGraph omega n).Adj f g) :
    (faceBoundaryGraph (crr_leftFill omega n)).Adj f g := by
  obtain ⟨p, q, hpq, hp, hq⟩ := h.2
  refine ⟨h.1.1, ?_⟩
  have hR := h.1.2
  rw [hpq, bdEdge_mk] at hR ⊢
  simp only [crr_leftFill, Set.mem_diff, hp, hq, true_and]
  tauto


theorem crr_LRFaceGraph_le_pmd
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    crr_LRFaceGraph omega n ≤ pmd_boxFaceBarrier omega n := by
  intro f g h
  obtain ⟨p, q, hpq, hp, hq⟩ := h.2
  exact crr_leftFill_faceBoundary_inBox_pmd omega n
    (crr_LRFaceGraph_adj_leftFill omega n h) hpq hp hq




theorem crr_leftFill_walk_lift (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {u v : Site 2}
    (w : (faceBoundaryGraph (crr_leftFill ω n)).Walk u v)
    (hint : ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g) :
    (pmd_boxFaceBarrier ω n).Reachable u v := by
  refine ⟨w.transfer (pmd_boxFaceBarrier ω n) ?_⟩
  intro e he
  refine e.ind (fun f g hfg => ?_) he
  rw [SimpleGraph.mem_edgeSet]
  obtain ⟨p, q, hpq, hp, hq⟩ := hint f g hfg
  exact crr_leftFill_faceBoundary_inBox_pmd ω n (w.adj_of_mem_edges hfg) hpq hp hq






theorem crr_closedBoundary_select_complementaryArc
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f₁ f₂ : Site 2}
    (c : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₁)
    (hf₂ : f₂ ∈ c.support)
    (hside :
      (∀ f g : Site 2, s(f, g) ∈ (c.takeUntil f₂ hf₂).edges →
        crc2_IsBoxInteriorEdge n f g) ∨
      (∀ f g : Site 2, s(f, g) ∈ (c.dropUntil f₂ hf₂).edges →
        crc2_IsBoxInteriorEdge n f g)) :
    ∃ w : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₂,
      ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g := by
  rcases hside with htake | hdrop
  · exact ⟨c.takeUntil f₂ hf₂, htake⟩
  · refine ⟨(c.dropUntil f₂ hf₂).reverse, ?_⟩
    intro f g hfg
    apply hdrop f g
    simpa [SimpleGraph.Walk.edges_reverse] using hfg







def crr_LeftFillFrameArcOrder (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (f₁ f₂ q₁ q₂ : Site 2),
    crr_InterfaceSideWith ω n f₁ q₁ → crr_InterfaceSideWith ω n f₂ q₂ →
    ∀ (h1 : q₁ ∈ bac_boxMinusL ω n) (h2 : q₂ ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨q₁, h1⟩ ⟨q₂, h2⟩ →
      ∃ c : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₁,
        ∃ hf₂ : f₂ ∈ c.support,
          (∀ f g : Site 2, s(f, g) ∈ (c.takeUntil f₂ hf₂).edges →
            crc2_IsBoxInteriorEdge n f g) ∨
          (∀ f g : Site 2, s(f, g) ∈ (c.dropUntil f₂ hf₂).edges →
            crc2_IsBoxInteriorEdge n f g)







def crr_LeftFillInteriorArc (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (f₁ f₂ q₁ q₂ : Site 2),
    crr_InterfaceSideWith ω n f₁ q₁ → crr_InterfaceSideWith ω n f₂ q₂ →
    ∀ (h1 : q₁ ∈ bac_boxMinusL ω n) (h2 : q₂ ∈ bac_boxMinusL ω n),
      ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Reachable ⟨q₁, h1⟩ ⟨q₂, h2⟩ →
      ∃ w : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₂,
        ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g


theorem crr_leftFillInteriorArc_of_frameArcOrder
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (horder : crr_LeftFillFrameArcOrder ω n) : crr_LeftFillInteriorArc ω n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  obtain ⟨c, hf₂c, hside⟩ := horder f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  exact crr_closedBoundary_select_complementaryArc ω n c hf₂c hside




theorem crr_interfaceCoastConnected_of_leftFillInteriorArc
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (harc : crr_LeftFillInteriorArc ω n) : crr_InterfaceCoastConnected ω n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  obtain ⟨w, hw⟩ := harc f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  exact crr_leftFill_walk_lift ω n w hw


theorem crr_interfaceCoastConnected_of_frameArcOrder
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (horder : crr_LeftFillFrameArcOrder ω n) : crr_InterfaceCoastConnected ω n :=
  crr_interfaceCoastConnected_of_leftFillInteriorArc ω n
    (crr_leftFillInteriorArc_of_frameArcOrder ω n horder)


theorem crr_leftFillInteriorArc
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
    crr_LeftFillInteriorArc omega n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ _h1 _h2 _hreach
  obtain ⟨u₁, hu₁, hfu₁, hinc₁⟩ := crr_interfaceSide_reaches_interior omega n hf₁
  obtain ⟨u₂, hu₂, hfu₂, hinc₂⟩ := crr_interfaceSide_reaches_interior omega n hf₂
  have huv := crr_interior_LRFaceGraph_reachable omega n hnoH hu₁ hu₂ hinc₁ hinc₂
  have hLR : (crr_LRFaceGraph omega n).Reachable f₁ f₂ :=
    hfu₁.trans (huv.trans hfu₂.symm)
  obtain ⟨w⟩ := hLR
  let wf : (faceBoundaryGraph (crr_leftFill omega n)).Walk f₁ f₂ :=
    w.transfer _ (fun e he => e.ind (fun f g hfg => by
      rw [SimpleGraph.mem_edgeSet]
      exact crr_LRFaceGraph_adj_leftFill omega n (w.adj_of_mem_edges hfg)) he)
  refine ⟨wf, ?_⟩
  intro f g hfg
  have hfg' : s(f, g) ∈ w.edges := by simpa [wf] using hfg
  exact (w.adj_of_mem_edges hfg').2




theorem crr_leftFillFrameArcOrder
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
    crr_LeftFillFrameArcOrder omega n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  obtain ⟨w, hw⟩ := crr_leftFillInteriorArc omega n hnoH
    f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  let c : (faceBoundaryGraph (crr_leftFill omega n)).Walk f₁ f₁ := w.append w.reverse
  have hf₂c : f₂ ∈ c.support :=
    w.subset_support_append_left w.reverse w.end_mem_support
  refine ⟨c, hf₂c, Or.inl ?_⟩
  intro f g hfg
  apply hw f g
  have hfgc : s(f, g) ∈ c.edges := c.edges_takeUntil_subset hf₂c hfg
  simpa [c, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse] using hfgc


theorem crr_interfaceCoastConnected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
    crr_InterfaceCoastConnected omega n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ _h1 _h2 _hreach
  obtain ⟨u₁, hu₁, hfu₁, hinc₁⟩ := crr_interfaceSide_reaches_interior omega n hf₁
  obtain ⟨u₂, hu₂, hfu₂, hinc₂⟩ := crr_interfaceSide_reaches_interior omega n hf₂
  have huv := crr_interior_LRFaceGraph_reachable omega n hnoH hu₁ hu₂ hinc₁ hinc₂
  exact hfu₁.trans (huv.trans hfu₂.symm) |>.mono (crr_LRFaceGraph_le_pmd omega n)


theorem crr_barrierConnectsRows_of_leftFillInteriorArc
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (harc : crr_LeftFillInteriorArc ω n) : pmd_BarrierConnectsRows ω n :=
  ccc_barrierConnectsRows_of_reachesBottom ω n hn hnoH
    (crr_reachesBottom_of_residue ω n hn hnoH
      (crr_interfaceCoastConnected_of_leftFillInteriorArc ω n harc))



theorem crr_barrierConnectsRows
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    pmd_BarrierConnectsRows ω n :=
  ccc_barrierConnectsRows_of_reachesBottom ω n hn hnoH
    (crr_reachesBottom_of_residue ω n hn hnoH
      (crr_interfaceCoastConnected ω n hnoH))





theorem crr_barrierFace_mem_faceRect
    (ω : ConfigSpace (Sym2 (Site 2))) (n a b : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (h : ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj ![a, b] g) :
    (![a, b] : Site 2) ∈ rect 0 (n - 1) (-1) n := by
  obtain ⟨u, v, hsides, hbd, hu, hv⟩ := crr_face_barrier_side ω n a b h
  rw [mem_rect]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [mem_rect] at hu hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    omega
  · rw [mem_rect] at hu hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    omega
  · rw [mem_rect] at hu hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    have ha0 : a ≠ 0 := by
      intro ha
      have huL : (![a, b] : Site 2) ∈ bcd_leftReach ω n :=
        jex_leftSide_subset_leftReach ω n ⟨hu, by simpa using ha⟩
      have hvL : (![a, b + 1] : Site 2) ∈ bcd_leftReach ω n :=
        jex_leftSide_subset_leftReach ω n ⟨hv, by simpa using ha⟩
      rw [bdEdge_mk] at hbd
      exact (hbd.mp huL) hvL
    have han : a ≠ n := by
      intro ha
      have huR : (![a, b] : Site 2) ∉ bcd_leftReach ω n :=
        jex_rightSide_notin_leftReach ω n hnoH ⟨hu, by simpa using ha⟩
      have hvR : (![a, b + 1] : Site 2) ∉ bcd_leftReach ω n :=
        jex_rightSide_notin_leftReach ω n hnoH ⟨hv, by simpa using ha⟩
      rw [bdEdge_mk] at hbd
      exact huR (hbd.mpr hvR)
    omega
  · rw [mem_rect] at hu hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    have ha0 : a + 1 ≠ 0 := by
      intro ha
      have huL : (![a + 1, b] : Site 2) ∈ bcd_leftReach ω n :=
        jex_leftSide_subset_leftReach ω n ⟨hu, by simpa using ha⟩
      have hvL : (![a + 1, b + 1] : Site 2) ∈ bcd_leftReach ω n :=
        jex_leftSide_subset_leftReach ω n ⟨hv, by simpa using ha⟩
      rw [bdEdge_mk] at hbd
      exact (hbd.mp huL) hvL
    omega



theorem crr_verticalCrossing_of_barrierConnectsRows
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hrows : pmd_BarrierConnectsRows ω n) :
    VerticalCrossing (fci_faceDualConfig ω) 0 (n - 1) (-1) n := by
  obtain ⟨a₀, a₁, ha0, ha0', ha1, ha1', hreach⟩ := hrows
  obtain ⟨w⟩ := hreach
  have hne : (![a₀, -1] : Site 2) ≠ ![a₁, n] := by
    intro heq
    have hcoord := congrFun heq 1
    have hminus : (-1 : ℤ) = n := by simpa using hcoord
    omega
  have hnonnil : ¬ w.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  let wopen : (openSubgraph 2 (fci_faceDualConfig ω)).Walk ![a₀, -1] ![a₁, n] :=
    w.transfer (openSubgraph 2 (fci_faceDualConfig ω)) (by
      intro e he
      refine e.ind (fun f g hfg => ?_) he
      rw [SimpleGraph.mem_edgeSet]
      have hopen := pmd_boxFaceBarrier_le_faceOpenDual ω n (w.adj_of_mem_edges hfg)
      rwa [fci_faceOpenDual_eq_openSubgraph] at hopen)
  have hsupport : ∀ z ∈ wopen.support, z ∈ rect 0 (n - 1) (-1) n := by
    intro z hz
    have hz' : z ∈ w.support := by simpa [wopen] using hz
    rw [w.mem_support_iff_exists_mem_edges_of_not_nil hnonnil] at hz'
    obtain ⟨e, he, hze⟩ := hz'
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hfg : (pmd_boxFaceBarrier ω n).Adj x y := w.adj_of_mem_edges he
      simp only [Sym2.mem_iff] at hze
      rcases hze with hzx | hzy
      · rw [hzx]
        let a := x 0
        let b := x 1
        have hfeq : x = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
        rw [hfeq]
        exact crr_barrierFace_mem_faceRect ω n a b hnoH ⟨y, by rwa [← hfeq]⟩
      · rw [hzy]
        let a := y 0
        let b := y 1
        have hgeq : y = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
        rw [hgeq]
        exact crr_barrierFace_mem_faceRect ω n a b hnoH ⟨x, by
          rw [← hgeq]
          exact hfg.symm⟩
  have hbot : (![a₀, -1] : Site 2) ∈ rect 0 (n - 1) (-1) n :=
    hsupport _ wopen.start_mem_support
  have htop : (![a₁, n] : Site 2) ∈ rect 0 (n - 1) (-1) n :=
    hsupport _ wopen.end_mem_support
  refine ⟨⟨![a₀, -1], hbot, by simp⟩, ⟨![a₁, n], htop, by simp⟩, ?_⟩
  exact walk_induce_reachable (openSubgraph 2 (fci_faceDualConfig ω))
    (rect 0 (n - 1) (-1) n) wopen hsupport hbot htop


theorem crr_horizontalCrossing_faceBand_subset (n : ℤ) (hn : 0 < n) :
    horizontalCrossingEvent 0 (n + 1) 0 (n - 1) ⊆
      horizontalCrossingEvent 0 (n + 1) 0 n := by
  intro eta heta
  obtain ⟨x, y, hxy⟩ := heta
  have hsub : rect 0 (n + 1) 0 (n - 1) ⊆ rect 0 (n + 1) 0 n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hx : (x : Site 2) ∈ rect 0 (n + 1) 0 n := hsub (leftSide_subset x.2)
  have hy : (y : Site 2) ∈ rect 0 (n + 1) 0 n := hsub (rightSide_subset y.2)
  refine ⟨⟨x, hx, x.2.2⟩, ⟨y, hy, y.2.2⟩, ?_⟩
  exact StatMech.RSW.Strip.connectedWithin_mono_set eta hsub hxy


def crr_FaceRectVerticalEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  verticalCrossingEvent 0 (n - 1) (-1) n


def crr_FaceDualRectEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  fci_faceDualConfig ⁻¹' crr_FaceRectVerticalEvent n


theorem crr_faceDualRect_half_law (n : ℤ)
    (hmeas : MeasurableSet (crr_FaceRectVerticalEvent n)) :
    rba_selfDualMeasure.real (crr_FaceDualRectEvent n) =
      rba_selfDualMeasure.real (crr_FaceRectVerticalEvent n) := by
  exact fci_faceDualConfig_measurePreserving.measureReal_preimage hmeas.nullMeasurableSet



theorem crr_faceRectVertical_real_le_square (n : ℤ) (hn : 0 < n)
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    rba_selfDualMeasure.real (crr_FaceRectVerticalEvent n) ≤
      rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  calc
    rba_selfDualMeasure.real (crr_FaceRectVerticalEvent n) =
        rba_selfDualMeasure.real (horizontalCrossingEvent (-1) n 0 (n - 1)) := by
      exact crf_verticalCrossing_eq_horizontal_swap 0 (n - 1) (-1) n hmeasThin
    _ = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 (n - 1)) := by
      symm
      simpa using cti_horizontalCrossing_translation_invariant (-1) n 0 (n - 1)
        (![1, 0] : Site 2) hmeasThin
    _ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) :=
      measureReal_mono (crr_horizontalCrossing_faceBand_subset n hn)
    _ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
      bxa_horizontalCrossing_real_mono_width hn (by omega)


theorem crr_square_compl_subset_faceDualRect (n : ℤ) (hn : 0 ≤ n)
    (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualRectEvent n := by
  intro ω hnoH
  apply crr_verticalCrossing_of_barrierConnectsRows ω n hnoH
  exact crr_barrierConnectsRows_of_leftFillInteriorArc ω n hn hnoH
    (crr_leftFillInteriorArc_of_frameArcOrder ω n (horder ω))



theorem crr_square_compl_subset_faceDualRect_unconditional (n : ℤ) (hn : 0 ≤ n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualRectEvent n := by
  intro ω hnoH
  exact crr_verticalCrossing_of_barrierConnectsRows ω n hnoH
    (crr_barrierConnectsRows ω n hn hnoH)



theorem crr_square_half_of_frameArcOrder (n : ℤ) (hn : 0 < n)
    (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ ≤
      rba_selfDualMeasure.real (crr_FaceDualRectEvent n) :=
    measureReal_mono (crr_square_compl_subset_faceDualRect n (le_of_lt hn) horder)
  rw [measureReal_compl hmeasH, probReal_univ,
    crr_faceDualRect_half_law n hmeasFace] at hmono
  have hcomp := crr_faceRectVertical_real_le_square n hn hmeasThin
  linarith



theorem crr_square_half (n : ℤ) (hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ ≤
      rba_selfDualMeasure.real (crr_FaceDualRectEvent n) :=
    measureReal_mono (crr_square_compl_subset_faceDualRect_unconditional n (le_of_lt hn))
  rw [measureReal_compl hmeasH, probReal_univ,
    crr_faceDualRect_half_law n hmeasFace] at hmono
  have hcomp := crr_faceRectVertical_real_le_square n hn hmeasThin
  linarith




def crr_FaceConnectionEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {eta | ∃ (a₀ a₁ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ n - 1 ∧
    (openSubgraph 2 eta).Reachable ![a₀, -1] ![a₁, n]}


def crr_FaceDualConnectionEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | pmd_FaceDualVCrossing ω n}



theorem crr_faceDualConnectionEvent_eq_preimage (n : ℤ) :
    crr_FaceDualConnectionEvent n =
      fci_faceDualConfig ⁻¹' crr_FaceConnectionEvent n := by
  ext ω
  change pmd_FaceDualVCrossing ω n ↔
    ∃ (a₀ a₁ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ n - 1 ∧
      (openSubgraph 2 (fci_faceDualConfig ω)).Reachable ![a₀, -1] ![a₁, n]
  unfold pmd_FaceDualVCrossing
  rw [fci_faceOpenDual_eq_openSubgraph]



theorem crr_faceDualConnection_half_law (n : ℤ)
    (hmeas : MeasurableSet (crr_FaceConnectionEvent n)) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one)
        (crr_FaceDualConnectionEvent n) =
      (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one)
        (crr_FaceConnectionEvent n) := by
  rw [crr_faceDualConnectionEvent_eq_preimage]
  exact fci_faceDualConfig_measurePreserving.measure_preimage hmeas.nullMeasurableSet



theorem crr_square_compl_subset_faceDualConnection (n : ℤ) (hn : 0 ≤ n)
    (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualConnectionEvent n := by
  intro ω hnoH
  exact crr_faceDualVCrossing_of_residue ω n hn hnoH
    (crr_interfaceCoastConnected_of_frameArcOrder ω n (horder ω))





theorem crr_square_half_of_frameArcOrder_and_faceComparison (n : ℤ) (hn : 0 ≤ n)
    (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceConnectionEvent n))
    (hcompare :
      (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real
          (crr_FaceConnectionEvent n) ≤
        (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real
          (horizontalCrossingEvent 0 n 0 n)) :
    (1 : ℝ) / 2 ≤
      (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real
        (horizontalCrossingEvent 0 n 0 n) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one
  have hmono : μ.real (horizontalCrossingEvent 0 n 0 n)ᶜ ≤
      μ.real (crr_FaceDualConnectionEvent n) :=
    measureReal_mono (crr_square_compl_subset_faceDualConnection n hn horder)
  have hlaw : μ.real (crr_FaceDualConnectionEvent n) =
      μ.real (crr_FaceConnectionEvent n) := by
    exact congrArg ENNReal.toReal (crr_faceDualConnection_half_law n hmeasFace)
  rw [measureReal_compl hmeasH, probReal_univ, hlaw] at hmono
  dsimp [μ] at hmono
  linarith


theorem crr_faceDualVCrossing_of_leftFillInteriorArc
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (harc : crr_LeftFillInteriorArc ω n) : pmd_FaceDualVCrossing ω n :=
  crr_faceDualVCrossing_of_residue ω n hn hnoH
    (crr_interfaceCoastConnected_of_leftFillInteriorArc ω n harc)







theorem crr_wall_frameFace_not_pmd_support :
    (![2, 0] : Site 2) ∉ (pmd_boxFaceBarrier bcc_wallCfg 2).support := by
  intro h
  rw [SimpleGraph.mem_support] at h
  obtain ⟨g, hg⟩ := h
  have hcol := bac_wall_barrierFace_col0 hg
  norm_num at hcol



theorem crr_wall_frameEdge_not_pmd_reachable :
    ¬ (pmd_boxFaceBarrier bcc_wallCfg 2).Reachable ![2, 0] ![2, -1] := by
  rintro ⟨w⟩
  have hne : (![2, 0] : Site 2) ≠ ![2, -1] := by
    intro h
    have := congrFun h 1
    norm_num at this
  obtain ⟨b, hab, p, rfl⟩ := w.exists_eq_cons_of_ne hne
  exact crr_wall_frameFace_not_pmd_support hab.mem_support_left

end Universality

end StatMech

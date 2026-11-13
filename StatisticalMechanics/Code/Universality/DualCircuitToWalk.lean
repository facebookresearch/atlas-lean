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
import Code.Lattice.Clusters
import Code.Lattice.FaceRegion
import Code.Lattice.JordanContour
import Code.Universality.BoxCrossingDichotomy

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}












def dcw_isBarrierEdge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (v w : Site 2) : Prop :=
  v ∈ bcd_leftReach ω n ∧ w ∈ rect 0 n 0 n ∧ w ∉ bcd_leftReach ω n ∧
    (hypercubicLattice 2).Adj v w


theorem dcw_barrier_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) : ω s(v, w) = false :=
  bcd_leftReach_boundary_closed ω n h.1 h.2.1 h.2.2.2 h.2.2.1



theorem dcw_barrier_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) : dualConfig ω (crossEdge s(v, w)) = true :=
  bcd_leftReach_boundary_dual_open ω n h.1 h.2.1 h.2.2.2 h.2.2.1




theorem dcw_barrier_dualAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) := by
  refine ⟨?_, ?_⟩
  · exact (rot90_adj v w).mpr h.2.2.2
  · have := dcw_barrier_dual_open ω n h
    rwa [crossEdge_mk] at this













theorem dcw_leftSide_in_L (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x : Site 2} (hx : x ∈ leftSide 0 n 0 n) :
    x ∈ bcd_leftReach ω n := by
  refine ⟨leftSide_subset hx, x, hx, leftSide_subset hx, ?_⟩
  exact connectedWithin_refl ω (rect 0 n 0 n) ⟨x, leftSide_subset hx⟩

theorem dcw_rightSide_notin_L (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {y : Site 2} (hy : y ∈ rightSide 0 n 0 n) :
    y ∉ bcd_leftReach ω n :=
  (bcd_no_horizontal_iff_right_unreachable ω n).mp hnoH y hy





theorem dcw_barrier_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n) :
    ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y :=
  not_reachable_latticeMinusBarrier (bcd_leftReach ω n)
    (dcw_leftSide_in_L ω n hx) (dcw_rightSide_notin_L ω n hnoH hy)




theorem dcw_leftRight_crossCount_odd (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n)
    (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount (bcd_leftReach ω n) w) := by
  rw [crossCount_parity]
  intro hiff
  exact dcw_rightSide_notin_L ω n hnoH hy (hiff.mp (dcw_leftSide_in_L ω n hx))










theorem dcw_primal_blocks_dual (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  StatMech.RSW.openWalk_blocks_dualWalk ω w w' e he he'






















def dcw_dualBarrierGraph (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    SimpleGraph (Site 2) where
  Adj p q :=
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧
      ((p = rot90Fun v ∧ q = rot90Fun w) ∨ (p = rot90Fun w ∧ q = rot90Fun v))
  symm := by
    rintro p q ⟨v, w, hvw, (⟨hp, hq⟩ | ⟨hp, hq⟩)⟩
    · exact ⟨v, w, hvw, Or.inr ⟨hq, hp⟩⟩
    · exact ⟨v, w, hvw, Or.inl ⟨hq, hp⟩⟩
  loopless := by
    refine ⟨fun p hp => ?_⟩
    have hinj : Function.Injective rot90Fun := rot90Equiv.injective
    rcases hp with ⟨v, w, hvw, (⟨hp, hq⟩ | ⟨hp, hq⟩)⟩
    · rw [hp] at hq
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 (hinj hq)
    · rw [hp] at hq
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 (hinj hq.symm)




theorem dcw_dualBarrierGraph_le_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    dcw_dualBarrierGraph ω n ≤ openSubgraph 2 (dualConfig ω) := by
  rintro p q ⟨v, w, hvw, hpq⟩
  have hopen : (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) :=
    dcw_barrier_dualAdj ω n hvw
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq]; exact hopen
  · rw [hp, hq]; exact hopen.symm




def dcw_dualBarrier_walk_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (c : (dcw_dualBarrierGraph ω n).Walk p q) :
    (openSubgraph 2 (dualConfig ω)).Walk p q :=
  c.mapLe (dcw_dualBarrierGraph_le_open ω n)


theorem dcw_dualBarrier_reachable_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (h : (dcw_dualBarrierGraph ω n).Reachable p q) :
    (openSubgraph 2 (dualConfig ω)).Reachable p q :=
  h.mono (dcw_dualBarrierGraph_le_open ω n)


































def dcw_BarrierRoute (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (p₀ : Site 2) (_hp₀ : p₀ ∈ bottomSide 0 n 0 n)
    (q₀ : Site 2) (_hq₀ : q₀ ∈ topSide 0 n 0 n)
    (c : (dcw_dualBarrierGraph ω n).Walk p₀ q₀),
    ∀ u ∈ c.support, u ∈ rect 0 n 0 n







theorem dcw_dualVerticalCrossing_of_route (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hroute : dcw_BarrierRoute ω n) :
    DualVerticalCrossing ω 0 n 0 n := by
  obtain ⟨p₀, hp₀, q₀, hq₀, c, hsupp⟩ := hroute
  
  set c' : (openSubgraph 2 (dualConfig ω)).Walk p₀ q₀ := dcw_dualBarrier_walk_open ω n c with hc'
  
  have hsupp' : c'.support = c.support := by
    rw [hc', dcw_dualBarrier_walk_open, SimpleGraph.Walk.support_mapLe_eq_support]
  have hsuppbox : ∀ u ∈ c'.support, u ∈ rect 0 n 0 n := by
    intro u hu; rw [hsupp'] at hu; exact hsupp u hu
  
  refine ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩, ?_⟩
  
  exact walk_induce_reachable (openSubgraph 2 (dualConfig ω)) (rect 0 n 0 n) c'
    hsuppbox (bottomSide_subset hp₀) (topSide_subset hq₀)

















theorem dcw_dualVertical_of_no_horizontal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hroute : dcw_BarrierRoute ω n) :
    DualVerticalCrossing ω 0 n 0 n :=
  dcw_dualVerticalCrossing_of_route ω n hroute







theorem dcw_square_dichotomy (n : ℤ)
    (hroute : ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ HorizontalCrossing ω 0 n 0 n → dcw_BarrierRoute ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n := by
  intro ω hω
  rw [Set.mem_compl_iff, mem_horizontalCrossingEvent] at hω
  rw [mem_dualVerticalCrossingEvent]
  exact dcw_dualVertical_of_no_horizontal ω n (hroute ω hω)










theorem dcw_dualBarrier_isOpenDual (n : ℤ)
    (hroute : ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ HorizontalCrossing ω 0 n 0 n → dcw_BarrierRoute ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n :=
  dcw_square_dichotomy n hroute
















theorem dcw_barrierEdge_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧ v 1 = 0 ∧ w 1 = 0 := by
  classical
  
  have hbl : (![0, 0] : Site 2) ∈ bcd_leftReach ω n := by
    apply dcw_leftSide_in_L
    refine ⟨⟨by simp, by simpa using hn, by simp, by simpa using hn⟩, by simp⟩
  have hbr : (![n, 0] : Site 2) ∉ bcd_leftReach ω n := by
    apply dcw_rightSide_notin_L ω n hnoH
    refine ⟨⟨by simpa using hn, by simp, by simp, by simpa using hn⟩, by simp⟩
  
  set P : ℕ → Prop := fun k => (![(k:ℤ), 0] : Site 2) ∈ bcd_leftReach ω n with hP
  have hP0 : P 0 := by simpa [hP] using hbl
  have hPn : ¬ P n.toNat := by
    have : ((n.toNat : ℤ)) = n := by omega
    simpa [hP, this] using hbr
  
  have hex : ∃ k, ¬ P k := ⟨n.toNat, hPn⟩
  set k := Nat.find hex with hk
  have hkfail : ¬ P k := Nat.find_spec hex
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hkfail; exact absurd hP0 hkfail
    · exact h0
  
  have hkprev : P (k - 1) := by
    by_contra hcon
    have : k ≤ k - 1 := Nat.find_le hcon
    omega
  
  refine ⟨![((k:ℤ) - 1), 0], ![(k:ℤ), 0], ?_, by simp, by simp⟩
  have hv : (![((k:ℤ) - 1), 0] : Site 2) ∈ bcd_leftReach ω n := by
    have hcast : ((k - 1 : ℕ) : ℤ) = (k:ℤ) - 1 := by omega
    rw [hP] at hkprev; rwa [hcast] at hkprev
  refine ⟨hv, ?_, ?_, ?_⟩
  · 
    have hvbox : (![((k:ℤ) - 1), 0] : Site 2) ∈ rect 0 n 0 n := hv.1
    rw [mem_rect] at hvbox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hvbox ⊢
    refine ⟨by omega, ?_, le_refl 0, hn⟩
    
    have hkle : k ≤ n.toNat := Nat.find_le hPn
    omega
  · 
    simpa [hP] using hkfail
  · 
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega




theorem dcw_dualBarrierGraph_nonempty_edge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ p q : Site 2, (dcw_dualBarrierGraph ω n).Adj p q := by
  obtain ⟨v, w, hbar, _, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact ⟨rot90Fun v, rot90Fun w, v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩

end Universality

end StatMech

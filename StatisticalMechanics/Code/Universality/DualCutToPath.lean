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
import Code.Universality.DualCircuitToWalk

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}














theorem dcp_barrier_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n) :
    ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y :=
  dcw_barrier_separates ω n hnoH hx hy














theorem dcp_topBarrierEdge_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧ v 1 = n ∧ w 1 = n := by
  classical
  
  have htl : (![0, n] : Site 2) ∈ bcd_leftReach ω n := by
    apply dcw_leftSide_in_L
    refine ⟨⟨by simp, by simpa using hn, by simpa using hn, by simp⟩, by simp⟩
  have htr : (![n, n] : Site 2) ∉ bcd_leftReach ω n := by
    apply dcw_rightSide_notin_L ω n hnoH
    refine ⟨⟨by simpa using hn, by simp, by simpa using hn, by simp⟩, by simp⟩
  
  set P : ℕ → Prop := fun k => (![(k:ℤ), n] : Site 2) ∈ bcd_leftReach ω n with hP
  have hP0 : P 0 := by simpa [hP] using htl
  have hPn : ¬ P n.toNat := by
    have : ((n.toNat : ℤ)) = n := by omega
    simpa [hP, this] using htr
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
  refine ⟨![((k:ℤ) - 1), n], ![(k:ℤ), n], ?_, by simp, by simp⟩
  have hv : (![((k:ℤ) - 1), n] : Site 2) ∈ bcd_leftReach ω n := by
    have hcast : ((k - 1 : ℕ) : ℤ) = (k:ℤ) - 1 := by omega
    rw [hP] at hkprev; rwa [hcast] at hkprev
  refine ⟨hv, ?_, ?_, ?_⟩
  · 
    have hvbox : (![((k:ℤ) - 1), n] : Site 2) ∈ rect 0 n 0 n := hv.1
    rw [mem_rect] at hvbox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hvbox ⊢
    refine ⟨by omega, ?_, hn, le_refl n⟩
    have hkle : k ≤ n.toNat := Nat.find_le hPn
    omega
  · simpa [hP] using hkfail
  · 
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega











theorem dcp_dualBarrierGraph_support (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (h : (dcw_dualBarrierGraph ω n).Adj p q) :
    p ∈ rot90Fun '' (rect 0 n 0 n) ∧ q ∈ rot90Fun '' (rect 0 n 0 n) := by
  obtain ⟨v, w, hvw, hpq⟩ := h
  have hvbox : v ∈ rect 0 n 0 n := hvw.1.1
  have hwbox : w ∈ rect 0 n 0 n := hvw.2.1
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact ⟨⟨v, hvbox, hp.symm⟩, ⟨w, hwbox, hq.symm⟩⟩
  · exact ⟨⟨w, hwbox, hp.symm⟩, ⟨v, hvbox, hq.symm⟩⟩




theorem dcp_dualBarrierGraph_finite_support (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    {p : Site 2 | ∃ q, (dcw_dualBarrierGraph ω n).Adj p q}.Finite := by
  apply Set.Finite.subset ((rect_finite 0 n 0 n).image rot90Fun)
  rintro p ⟨q, hpq⟩
  exact (dcp_dualBarrierGraph_support ω n hpq).1






















def dcp_DualCutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (p₀ : Site 2) (_hp₀ : p₀ ∈ bottomSide 0 n 0 n)
    (q₀ : Site 2) (_hq₀ : q₀ ∈ topSide 0 n 0 n)
    (c : (dcw_dualBarrierGraph ω n).Walk p₀ q₀),
    ∀ u ∈ c.support, u ∈ rect 0 n 0 n





theorem dcp_route_of_cutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hcut : dcp_DualCutConnects ω n) : dcw_BarrierRoute ω n :=
  hcut





theorem dcp_dualVerticalCrossing_of_cutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hcut : dcp_DualCutConnects ω n) :
    DualVerticalCrossing ω 0 n 0 n :=
  dcw_dualVerticalCrossing_of_route ω n (dcp_route_of_cutConnects ω n hcut)






theorem dcp_dichotomy_of_cutConnects (n : ℤ)
    (hcut : ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ HorizontalCrossing ω 0 n 0 n → dcp_DualCutConnects ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n :=
  dcw_square_dichotomy n (fun ω hω => dcp_route_of_cutConnects ω n (hcut ω hω))

















theorem dcp_bottomBarrierVertex_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v : Site 2, v 1 = 0 ∧ (∃ q, (dcw_dualBarrierGraph ω n).Adj (rot90Fun v) q) := by
  obtain ⟨v, w, hbar, hv0, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact ⟨v, hv0, rot90Fun w, v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩




theorem dcp_topBarrierVertex_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v : Site 2, v 1 = n ∧ (∃ q, (dcw_dualBarrierGraph ω n).Adj (rot90Fun v) q) := by
  obtain ⟨v, w, hbar, hvn, _⟩ := dcp_topBarrierEdge_exists ω n hn hnoH
  exact ⟨v, hvn, rot90Fun w, v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩















theorem dcp_rot90_bottomRow (a : ℤ) : rot90Fun ![a, 0] = ![0, a] := by
  simp



theorem dcp_rot90_topRow (a n : ℤ) : rot90Fun ![a, n] = ![-n, a] := by
  simp






















def dcp_CutReachable (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (p₀ : Site 2) (_hp₀ : p₀ ∈ bottomSide 0 n 0 n)
    (q₀ : Site 2) (_hq₀ : q₀ ∈ topSide 0 n 0 n),
    (dcw_dualBarrierGraph ω n).Reachable p₀ q₀





theorem dcp_cutReachable_of_cutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hcut : dcp_DualCutConnects ω n) : dcp_CutReachable ω n := by
  obtain ⟨p₀, hp₀, q₀, hq₀, c, _⟩ := hcut
  exact ⟨p₀, hp₀, q₀, hq₀, c.reachable⟩







theorem dcp_dualOpen_reachable_of_cutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hcut : dcp_DualCutConnects ω n) :
    ∃ (p₀ : Site 2) (_hp₀ : p₀ ∈ bottomSide 0 n 0 n)
      (q₀ : Site 2) (_hq₀ : q₀ ∈ topSide 0 n 0 n),
      (openSubgraph 2 (dualConfig ω)).Reachable p₀ q₀ := by
  obtain ⟨p₀, hp₀, q₀, hq₀, c, _⟩ := hcut
  exact ⟨p₀, hp₀, q₀, hq₀, dcw_dualBarrier_reachable_open ω n c.reachable⟩























theorem dcp_dualBarrierGraph_support_rot (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (h : (dcw_dualBarrierGraph ω n).Adj p q) :
    p ∈ rect (-n) 0 0 n := by
  obtain ⟨v, w, hvw, hpq⟩ := h
  have hvbox : v ∈ rect 0 n 0 n := hvw.1.1
  have hwbox : w ∈ rect 0 n 0 n := hvw.2.1
  rw [mem_rect] at hvbox hwbox
  have hrot : ∀ x : Site 2, x ∈ rect 0 n 0 n → rot90Fun x ∈ rect (-n) 0 0 n := by
    intro x hx
    rw [mem_rect] at hx
    rw [mem_rect, rot90Fun]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  rcases hpq with ⟨hp, _⟩ | ⟨hp, _⟩
  · rw [hp]; exact hrot v hvbox
  · rw [hp]; exact hrot w hwbox



theorem dcp_rot90_leftSide (n : ℤ) {x : Site 2} (hx : x ∈ leftSide 0 n 0 n) :
    rot90Fun x ∈ bottomSide (-n) 0 0 n := by
  obtain ⟨hbox, h0⟩ := hx
  rw [mem_rect] at hbox
  have hsnd : (rot90Fun x) 1 = x 0 := by rw [rot90Fun]; rfl
  refine ⟨?_, ?_⟩
  · rw [mem_rect, rot90Fun]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [hsnd, h0]



theorem dcp_rot90_rightSide (n : ℤ) {x : Site 2} (hx : x ∈ rightSide 0 n 0 n) :
    rot90Fun x ∈ topSide (-n) 0 0 n := by
  obtain ⟨hbox, hn⟩ := hx
  rw [mem_rect] at hbox
  have hsnd : (rot90Fun x) 1 = x 0 := by rw [rot90Fun]; rfl
  refine ⟨?_, ?_⟩
  · rw [mem_rect, rot90Fun]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [hsnd, hn]








def dcp_DualCutConnectsRot (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (p₀ : Site 2) (_hp₀ : p₀ ∈ bottomSide (-n) 0 0 n)
    (q₀ : Site 2) (_hq₀ : q₀ ∈ topSide (-n) 0 0 n),
    (dcw_dualBarrierGraph ω n).Reachable p₀ q₀





theorem dcp_barrierWalk_support_rot (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (c : (dcw_dualBarrierGraph ω n).Walk p q) (hp : p ∈ rect (-n) 0 0 n) :
    ∀ u ∈ c.support, u ∈ rect (-n) 0 0 n := by
  induction c with
  | nil => intro u hu; rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu; rwa [hu]
  | @cons a b d hab p ih =>
    intro u hu
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact hp
    · exact ih (dcp_dualBarrierGraph_support_rot ω n hab.symm) u hu







theorem dcp_rotatedDualVerticalCrossing_of_cutConnectsRot
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hcut : dcp_DualCutConnectsRot ω n) :
    DualVerticalCrossing ω (-n) 0 0 n := by
  obtain ⟨p₀, hp₀, q₀, hq₀, hreach⟩ := hcut
  rw [dualVerticalCrossing_iff]
  
  obtain ⟨c⟩ := hreach
  set c' : (openSubgraph 2 (dualConfig ω)).Walk p₀ q₀ := dcw_dualBarrier_walk_open ω n c
    with hc'
  
  have hsupp' : c'.support = c.support := by
    rw [hc', dcw_dualBarrier_walk_open, SimpleGraph.Walk.support_mapLe_eq_support]
  have hsuppbox : ∀ u ∈ c'.support, u ∈ rect (-n) 0 0 n := by
    intro u hu
    rw [hsupp'] at hu
    exact dcp_barrierWalk_support_rot ω n c (bottomSide_subset hp₀) u hu
  refine ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩, ?_⟩
  exact walk_induce_reachable (openSubgraph 2 (dualConfig ω)) (rect (-n) 0 0 n) c'
    hsuppbox (bottomSide_subset hp₀) (topSide_subset hq₀)






















theorem dcp_rotatedCut_nonempty_edge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ p q : Site 2, (dcw_dualBarrierGraph ω n).Adj p q ∧
      p ∈ rect (-n) 0 0 n ∧ q ∈ rect (-n) 0 0 n := by
  obtain ⟨p, q, hpq⟩ := dcw_dualBarrierGraph_nonempty_edge ω n hn hnoH
  exact ⟨p, q, hpq, dcp_dualBarrierGraph_support_rot ω n hpq,
    dcp_dualBarrierGraph_support_rot ω n hpq.symm⟩

end Universality

end StatMech

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
import Code.Lattice.CrossingParity
import Code.Lattice.JordanSeparationFinish
import Code.Lattice.JordanEulerInduction
import Code.Lattice.JordanBridgeCycle

open SimpleGraph Set

namespace StatMech

namespace Lattice












theorem whb_crossEdge_endpoints (a b : Site 2) :
    crossEdge s(a, b) = s(rot90Fun a, rot90Fun b) := crossEdge_mk a b




theorem whb_crossEdge_symm_straddle (f g : Site 2) :
    crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := jbc_crossEdge_symm_pair f g












theorem whb_imageGraph_square :
    imageGraph jbc_Pce = jei_pushGraph jbc_Pce jbc_cyc4 :=
  (jei_pushGraph_G jbc_Pce).symm




theorem whb_reg_adj_of_straddle_ym1 {f g : Site 2}
    (hadj : (hypercubicLattice 2).Adj f g) (h : (rot90Inv f) 1 = -1 ∨ (rot90Inv g) 1 = -1) :
    (regionGraph (imageGraph jbc_Pce)).Adj f g := by
  rw [regionGraph_adj]
  refine ⟨hadj, ?_⟩
  rw [whb_imageGraph_square]
  rcases h with h | h
  · exact jbc_not_contour_ym1 h
  · exact jbc_not_contour_ym1' h


theorem whb_latadj {a b : Site 2} (h : (∑ i, (a i - b i).natAbs) = 1) :
    (hypercubicLattice 2).Adj a b := by rw [hypercubicLattice_adj]; exact h


theorem whb_csq_x (i : Fin 4) : (jbc_csq i) 0 = 0 ∨ (jbc_csq i) 0 = 1 := by
  fin_cases i <;> simp [jbc_csq]



theorem whb_pushed_corner {u v : Site 2} (h : (jei_pushGraph jbc_Pce jbc_cyc4).Adj u v) :
    (u 0 = 0 ∨ u 0 = 1) ∧ (u 1 = 0 ∨ u 1 = 1) := by
  obtain ⟨i, j, _, hi, _⟩ := h
  have hu : jbc_csq i = u := hi
  rw [← hu]
  exact ⟨whb_csq_x i, jbc_csq_y i⟩




theorem whb_east_step_safe (a b : ℤ) (h : ¬ (a = -1 ∧ (b = 0 ∨ b = 1))) :
    (regionGraph (imageGraph jbc_Pce)).Adj ![a, b] ![a + 1, b] := by
  rw [regionGraph_adj]
  refine ⟨whb_latadj (by rw [Fin.sum_univ_two]; norm_num), ?_⟩
  rw [whb_imageGraph_square, whb_crossEdge_symm_straddle,
    rot90Inv_apply, rot90Inv_apply, SimpleGraph.mem_edgeSet]
  intro hpush
  
  have hc1 := whb_pushed_corner hpush
  
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc1
  
  obtain ⟨hb, ha⟩ := hc1
  
  have hc2 := whb_pushed_corner hpush.symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc2
  obtain ⟨_, ha2⟩ := hc2
  
  refine h ⟨?_, ?_⟩ <;> omega





theorem whb_south_step_safe (a b : ℤ) (hsafe : ¬ (b = 1 ∧ (a = 0 ∨ a = -1))) :
    (regionGraph (imageGraph jbc_Pce)).Adj ![a, b] ![a, b - 1] := by
  rw [regionGraph_adj]
  refine ⟨whb_latadj (by rw [Fin.sum_univ_two]; norm_num), ?_⟩
  rw [whb_imageGraph_square, whb_crossEdge_symm_straddle,
    rot90Inv_apply, rot90Inv_apply, SimpleGraph.mem_edgeSet]
  intro hpush
  have hc1 := whb_pushed_corner hpush
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc1
  obtain ⟨hb0, ha0⟩ := hc1
  have hc2 := whb_pushed_corner hpush.symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc2
  obtain ⟨hb1, _⟩ := hc2
  
  exact hsafe ⟨by omega, by omega⟩




theorem whb_north_step_safe (a b : ℤ) (hb : b ≠ 0) :
    (regionGraph (imageGraph jbc_Pce)).Adj ![a, b] ![a, b + 1] := by
  rw [regionGraph_adj]
  refine ⟨whb_latadj (by rw [Fin.sum_univ_two]; norm_num), ?_⟩
  rw [whb_imageGraph_square, whb_crossEdge_symm_straddle,
    rot90Inv_apply, rot90Inv_apply, SimpleGraph.mem_edgeSet]
  intro hpush
  have hc1 := whb_pushed_corner hpush
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc1
  obtain ⟨hb0, _⟩ := hc1
  have hc2 := whb_pushed_corner hpush.symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc2
  obtain ⟨hb1, _⟩ := hc2
  
  omega




theorem whb_west_step_safe (a b : ℤ) (ha : a ≠ 0) :
    (regionGraph (imageGraph jbc_Pce)).Adj ![a, b] ![a - 1, b] := by
  rw [regionGraph_adj]
  refine ⟨whb_latadj (by rw [Fin.sum_univ_two]; norm_num), ?_⟩
  rw [whb_imageGraph_square, whb_crossEdge_symm_straddle,
    rot90Inv_apply, rot90Inv_apply, SimpleGraph.mem_edgeSet]
  intro hpush
  have hc1 := whb_pushed_corner hpush
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc1
  obtain ⟨_, ha0⟩ := hc1
  have hc2 := whb_pushed_corner hpush.symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc2
  obtain ⟨_, ha2⟩ := hc2
  
  omega









theorem whb_up_to_m2 (a : ℤ) : ∀ n : ℕ,
    (regionGraph (imageGraph jbc_Pce)).Reachable ![a, -2 - (n : ℤ)] ![a, -2] := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, sub_zero]
  | succ m ih =>
    have hstep : (regionGraph (imageGraph jbc_Pce)).Adj
        ![a, -2 - ((m : ℤ) + 1)] ![a, -2 - ((m : ℤ) + 1) + 1] :=
      whb_north_step_safe a (-2 - ((m : ℤ) + 1)) (by omega)
    have : (-2 - ((m : ℤ) + 1) + 1) = -2 - (m : ℤ) := by ring
    rw [this] at hstep
    have hcast : (-2 - (((m : ℕ) + 1 : ℕ) : ℤ)) = -2 - ((m : ℤ) + 1) := by push_cast; ring
    rw [hcast]
    exact hstep.reachable.trans ih


theorem whb_south_reach (a b : ℤ) (hsafe : ¬ (b = 1 ∧ (a = 0 ∨ a = -1))) :
    (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![a, b - 1] :=
  (whb_south_step_safe a b hsafe).reachable



theorem whb_south_escape (a b : ℤ) (hb : b ≤ 0) :
    (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![a, -2] := by
  rcases lt_or_ge b (-1) with hlt | hge
  · 
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = -2 - (n : ℤ) := ⟨(-2 - b).toNat, by omega⟩
    subst hn; exact whb_up_to_m2 a n
  · 
    interval_cases b
    · have h := whb_south_reach a (-1) (by rintro ⟨h, _⟩; omega)
      rw [show (-1 : ℤ) - 1 = -2 by norm_num] at h; exact h
    · have h0 := whb_south_reach a 0 (by rintro ⟨h, _⟩; omega)
      have h1 := whb_south_reach a (-1) (by rintro ⟨h, _⟩; omega)
      rw [show (0 : ℤ) - 1 = -1 by norm_num] at h0
      rw [show (-1 : ℤ) - 1 = -2 by norm_num] at h1
      exact h0.trans h1



theorem whb_east_reach_m2 (a : ℤ) :
    (regionGraph (imageGraph jbc_Pce)).Reachable ![a, -2] ![a + 1, -2] :=
  (whb_east_step_safe a (-2) (by rintro ⟨_, h | h⟩ <;> omega)).reachable


theorem whb_row_to_beacon (a : ℤ) :
    (regionGraph (imageGraph jbc_Pce)).Reachable ![a, -2] ![0, -2] := by
  rcases le_or_gt 0 a with hge | hlt
  · 
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a = (n : ℤ) := ⟨a.toNat, by omega⟩
    subst hn; clear hge
    induction n with
    | zero => rw [Nat.cast_zero]
    | succ m ih =>
      have hstep := whb_east_reach_m2 (m : ℤ)
      have hcast : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at hstep
      exact hstep.symm.trans ih
  · 
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
    subst hn; clear hlt
    induction n with
    | zero => rw [Nat.cast_zero, neg_zero]
    | succ m ih =>
      have hstep := whb_east_reach_m2 (-((m : ℤ) + 1))
      have heq : (-((m : ℤ) + 1) + 1) = -(m : ℤ) := by ring
      rw [heq] at hstep
      have hcast : (-(((m + 1 : ℕ)) : ℤ)) = -((m : ℤ) + 1) := by push_cast; ring
      rw [hcast]
      exact hstep.trans ih



theorem whb_descend_safe_col (a : ℤ) (ha : a ≠ 0 ∧ a ≠ -1) (b : ℤ) :
    (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![a, -2] := by
  rcases le_or_gt b 0 with hb | hb
  · exact whb_south_escape a b hb
  · 
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = (n : ℤ) := ⟨b.toNat, by omega⟩
    subst hn
    clear hb
    have hto0 : (regionGraph (imageGraph jbc_Pce)).Reachable ![a, (n : ℤ)] ![a, 0] := by
      induction n with
      | zero => rw [Nat.cast_zero]
      | succ m ih =>
        have hstep : (regionGraph (imageGraph jbc_Pce)).Adj
            ![a, ((m : ℤ) + 1)] ![a, ((m : ℤ) + 1) - 1] :=
          whb_south_step_safe a ((m : ℤ) + 1) (by rintro ⟨_, h | h⟩ <;> omega)
        have heq : (((m : ℤ) + 1) - 1) = (m : ℤ) := by ring
        rw [heq] at hstep
        have hcast : (((m + 1 : ℕ)) : ℤ) = ((m : ℤ) + 1) := by push_cast; ring
        rw [hcast]
        exact hstep.reachable.trans ih
    exact hto0.trans (whb_south_escape a 0 (by norm_num))





theorem whb_reaches_row (a b : ℤ) :
    ∃ a' : ℤ, (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![a', -2] := by
  by_cases hcol : a = 0 ∨ a = -1
  · 
    rcases hcol with rfl | rfl
    · 
      have hstep : (regionGraph (imageGraph jbc_Pce)).Adj ![(0 : ℤ), b] ![0 + 1, b] :=
        whb_east_step_safe 0 b (by rintro ⟨h, _⟩; omega)
      rw [show (0 : ℤ) + 1 = 1 by norm_num] at hstep
      exact ⟨1, hstep.reachable.trans (whb_descend_safe_col 1 ⟨by norm_num, by norm_num⟩ b)⟩
    · 
      have hstep : (regionGraph (imageGraph jbc_Pce)).Adj ![(-1 : ℤ), b] ![(-1) - 1, b] :=
        whb_west_step_safe (-1) b (by norm_num)
      rw [show (-1 : ℤ) - 1 = -2 by norm_num] at hstep
      exact ⟨-2, hstep.reachable.trans (whb_descend_safe_col (-2) ⟨by norm_num, by norm_num⟩ b)⟩
  · push Not at hcol
    exact ⟨a, whb_descend_safe_col a hcol b⟩



theorem whb_reaches_beacon (a b : ℤ) :
    (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![0, -2] := by
  obtain ⟨a', h⟩ := whb_reaches_row a b
  exact h.trans (whb_row_to_beacon a')





theorem whb_square_regionGraph_connected (x y : Site 2) :
    (regionGraph (imageGraph jbc_Pce)).Reachable x y := by
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  have hy : y = ![y 0, y 1] := by funext i; fin_cases i <;> rfl
  rw [hx, hy]
  exact (whb_reaches_beacon (x 0) (x 1)).trans (whb_reaches_beacon (y 0) (y 1)).symm



theorem whb_square_card_components :
    Nat.card (regionGraph (imageGraph jbc_Pce)).ConnectedComponent = 1 := by
  have hsub : Subsingleton (regionGraph (imageGraph jbc_Pce)).ConnectedComponent :=
    ⟨ConnectedComponent.ind₂
      (fun a b => ConnectedComponent.sound (whb_square_regionGraph_connected a b))⟩
  haveI : Nonempty (regionGraph (imageGraph jbc_Pce)).ConnectedComponent :=
    ⟨(regionGraph (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨hsub, inferInstance⟩










theorem whb_square_faceCount : faceCount jbc_cyc4 = 2 := by
  have hV : Nat.card (Fin 4) = 4 := by simp
  have hE : jbc_cyc4.edgeSet.ncard = 4 := by
    have : jbc_cyc4.edgeSet = {s(0, 1), s(1, 2), s(2, 3), s(3, 0)} := by
      ext e; obtain ⟨u, v⟩ := e
      rw [SimpleGraph.mem_edgeSet, jbc_cyc4_adj]
      constructor
      · intro h; fin_cases u <;> fin_cases v <;>
          simp_all [jbc_cyc4Rel]
      · intro h; fin_cases u <;> fin_cases v <;>
          simp_all [jbc_cyc4Rel]
    rw [this]
    rw [Set.ncard_eq_toFinset_card']
    decide
  have hC : Nat.card jbc_cyc4.ConnectedComponent = 1 := by
    have hconn : ∀ i j : Fin 4, jbc_cyc4.Reachable i j := by
      have a01 : jbc_cyc4.Adj 0 1 := by rw [jbc_cyc4_adj]; decide
      have a12 : jbc_cyc4.Adj 1 2 := by rw [jbc_cyc4_adj]; decide
      have a23 : jbc_cyc4.Adj 2 3 := by rw [jbc_cyc4_adj]; decide
      intro i j
      have r0 : ∀ k : Fin 4, jbc_cyc4.Reachable 0 k := by
        intro k; fin_cases k
        · exact Reachable.refl _
        · exact a01.reachable
        · exact a01.reachable.trans a12.reachable
        · exact a01.reachable.trans (a12.reachable.trans a23.reachable)
      exact (r0 i).symm.trans (r0 j)
    have hsub : Subsingleton jbc_cyc4.ConnectedComponent :=
      ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hconn a b))⟩
    rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, ⟨jbc_cyc4.connectedComponentMk 0⟩⟩
  unfold faceCount nullity
  rw [hE, hC, hV]














theorem whb_planarCutCycleDuality_square_false :
    ¬ jsf_PlanarCutCycleDuality jbc_Pce := by
  unfold jsf_PlanarCutCycleDuality
  rw [whb_square_card_components]
  show ¬ (1 = faceCount jbc_Pce.G)
  change ¬ (1 = faceCount jbc_cyc4)
  rw [whb_square_faceCount]
  decide














noncomputable def whb_faceRegion (G : SimpleGraph (Site 2)) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∉ G.edgeSet
  symm := by
    intro f g ⟨hadj, hs⟩
    exact ⟨hadj.symm, by rwa [sharedPrimalEdge_comm_of_adj hadj] at hs⟩
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem whb_faceRegion_adj (G : SimpleGraph (Site 2)) (f g : Site 2) :
    (whb_faceRegion G).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∉ G.edgeSet := Iff.rfl


theorem whb_square_edge_mem {u v : Fin 4} (h : jbc_cyc4.Adj u v) :
    s(jbc_csq u, jbc_csq v) ∈ (imageGraph jbc_Pce).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  exact ⟨u, v, h, rfl, rfl⟩






theorem whb_faceRegion_interior_isolated (g : Site 2) :
    ¬ (whb_faceRegion (imageGraph jbc_Pce)).Adj ![0, 0] g := by
  rintro ⟨hadj, hshared⟩
  apply hshared
  
  
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
  
  have h00 : (![0, 0] : Site 2) 0 = 0 := rfl
  have h01 : (![0, 0] : Site 2) 1 = 0 := rfl
  rw [h00, h01] at hadj
  
  have : (g 0 = 1 ∧ g 1 = 0) ∨ (g 0 = -1 ∧ g 1 = 0) ∨
      (g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 0 ∧ g 1 = -1) := by omega
  rcases this with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![1, 0] : Site 2) = ![(0 : ℤ) + 1, 0] by norm_num, sharedPrimalEdge_right]
    exact whb_square_edge_mem (u := 1) (v := 2) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![-1, 0] : Site 2) = ![(0 : ℤ) - 1, 0] by norm_num, sharedPrimalEdge_left]
    exact whb_square_edge_mem (u := 0) (v := 3) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![0, 1] : Site 2) = ![(0 : ℤ), 0 + 1] by norm_num, sharedPrimalEdge_top]
    exact whb_square_edge_mem (u := 3) (v := 2) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![0, -1] : Site 2) = ![(0 : ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    exact whb_square_edge_mem (u := 0) (v := 1) (by rw [jbc_cyc4_adj]; decide)






theorem whb_faceRegion_interior_supp :
    ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp = {![0, 0]} := by
  ext x
  rw [ConnectedComponent.mem_supp_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    
    rw [ConnectedComponent.eq] at h
    obtain ⟨w⟩ := h.symm
    cases w with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (whb_faceRegion_interior_isolated _)
  · rintro rfl; rfl



theorem whb_faceRegion_interior_bounded :
    ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp.Finite := by
  rw [whb_faceRegion_interior_supp]; exact Set.finite_singleton _



















def whb_CorrectWhitney : Prop :=
  ∀ (H : SimpleGraph (Site 2)) (p q f g : Site 2),
    (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
    (hypercubicLattice 2).Adj f g → sharedPrimalEdge f g = s(p, q) →
    (H.Reachable p q ↔
      ¬ ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable f g)







theorem whb_correctModel_square_separates :
    (∀ g, ¬ (whb_faceRegion (imageGraph jbc_Pce)).Adj ![0, 0] g) ∧
      ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp.Finite :=
  ⟨whb_faceRegion_interior_isolated, whb_faceRegion_interior_bounded⟩















theorem whb_loop_crossing_even (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) : Even (crossCount S w) :=
  crossCount_even_of_loop S w






theorem whb_barrier_separates (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount S w) :=
  crossCount_odd_of_separated S hx hy w






theorem whb_latticeMinusBarrier_separates (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) :
    ¬ (latticeMinusBarrier S).Reachable x y :=
  not_reachable_latticeMinusBarrier S hx hy

end Lattice

end StatMech

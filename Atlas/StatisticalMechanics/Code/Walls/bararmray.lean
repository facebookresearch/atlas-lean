/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Walls.bc34ray
import Code.Walls.bc67supervertex
import Code.Walls.bgctrifgraph

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}
















theorem bar_armRay_of_infiniteComponent (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ r : ℕ → Site d, r 0 = a ∧ Function.Injective r ∧
      (∀ k, (bc67_contractedLattice ω L y).Adj (r k) (r (k + 1))) ∧
      (∀ k, (bc67_contractedLattice ω L y).Reachable a (r k)) := by
  classical
  set ω' : ConfigSpace (Sym2 (Site d)) := removeSites (bc61_boxAround d L y) ω with hω'
  have hG : bc67_contractedLattice ω L y = openSubgraph d ω' := rfl
  
  have hinf' : (ray34_AvoidCluster (openSubgraph d ω') ∅ a).Infinite := by
    rw [ray34_avoidCluster_empty_eq_cluster]; exact hinf
  have ha : a ∉ (∅ : Set (Site d)) := Set.notMem_empty a
  obtain ⟨r, hr0, hinj, hadj, -⟩ := ray34_konig (openSubgraph d ω') ha hinf'
  refine ⟨r, hr0, hinj, ?_, ?_⟩
  · intro k; rw [hG]; exact hadj k
  · 
    intro k
    rw [hG]
    induction k with
    | zero => rw [hr0]
    | succ n ih => exact ih.trans (hadj n).reachable













theorem bar_boxAvoiding_armRay (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) (T : Finset (Site d)) :
    ∃ b : Site d, (bc67_contractedLattice ω L y).Reachable a b ∧
      ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧
        (∀ k, (bc67_contractedLattice ω L y).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ T) := by
  classical
  set ω' : ConfigSpace (Sym2 (Site d)) := removeSites (bc61_boxAround d L y) ω with hω'
  have hG : bc67_contractedLattice ω L y = openSubgraph d ω' := rfl
  have hinf' : (ray34_AvoidCluster (openSubgraph d ω') ∅ a).Infinite := by
    rw [ray34_avoidCluster_empty_eq_cluster]; exact hinf
  obtain ⟨b, hbmem, hbinf⟩ := ray34_infinite_avoidCluster_of_finset hinf' T
  have hbT : b ∉ (↑T : Set (Site d)) := ray34_notMem_of_avoidCluster_nonempty hbinf.nonempty
  obtain ⟨r, hr0, hinj, hadj, hravoid⟩ := ray34_konig (openSubgraph d ω') hbT hbinf
  refine ⟨b, ?_, r, hr0, hinj, ?_, ?_⟩
  · rw [hG]
    obtain ⟨p, -⟩ := (ray34_mem_avoidCluster.mp hbmem)
    exact p.reachable
  · intro k; rw [hG]; exact hadj k
  · intro k; have := hravoid k; rwa [Finset.mem_coe] at this



theorem bar_ray_exits_box (r : ℕ → Site d) (hinj : Function.Injective r) (R : ℕ) :
    ∃ k, r k ∉ box d R := by
  by_contra h
  push_neg at h
  have hsub : Set.range r ⊆ box d R := by rintro _ ⟨k, rfl⟩; exact h k
  exact (Set.infinite_range_of_injective hinj) ((box_finite d R).subset hsub)






theorem bar_ray_crosses_boundary (r : ℕ → Site d) (hinj : Function.Injective r)
    (hadj : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)))
    (R : ℕ) (hR : 1 ≤ R) (h0 : r 0 ∈ box d R) :
    ∃ k, r k ∈ vertexBoundary d R := by
  classical
  have hex : ∃ k, r k ∉ box d R := bar_ray_exits_box r hinj R
  set k := Nat.find hex with hkdef
  have hk : r k ∉ box d R := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hle
    push_neg at hle
    have hk0 : k = 0 := Nat.le_zero.mp hle
    rw [hk0] at hk
    exact hk h0
  set m := k - 1 with hmdef
  have hmk : m + 1 = k := Nat.succ_pred_eq_of_pos hkpos
  
  have hmbox : r m ∈ box d R := by
    have hmlt : m < k := by omega
    have := Nat.find_min hex hmlt
    simpa using this
  
  have hm1 : r (m + 1) ∉ box d R := by rw [hmk]; exact hk
  
  have hsum : (∑ i, (r m i - r (m + 1) i).natAbs) = 1 := by
    have := hadj m; rwa [hypercubicLattice_adj] at this
  
  obtain ⟨j, hj⟩ : ∃ j, R + 1 ≤ (r (m + 1) j).natAbs := by
    rw [mem_box] at hm1; push_neg at hm1
    obtain ⟨j, hj⟩ := hm1; exact ⟨j, by omega⟩
  
  have hstep : (r m j - r (m + 1) j).natAbs ≤ 1 := by
    calc (r m j - r (m + 1) j).natAbs
        ≤ ∑ i, (r m i - r (m + 1) i).natAbs :=
          Finset.single_le_sum (f := fun i => (r m i - r (m + 1) i).natAbs)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      _ = 1 := hsum
  
  have htri : (r (m + 1) j).natAbs ≤ (r m j).natAbs + (r m j - r (m + 1) j).natAbs := by
    have h := Int.natAbs_sub_le (r m j) (r m j - r (m + 1) j)
    simpa [sub_sub_cancel] using h
  have hRj : R ≤ (r m j).natAbs := by omega
  have hjbox : (r m j).natAbs ≤ R := by rw [mem_box] at hmbox; exact hmbox j
  have hjeq : (r m j).natAbs = R := le_antisymm hjbox hRj
  refine ⟨m, ?_⟩
  rw [mem_vertexBoundary]
  refine ⟨hmbox, ?_⟩
  rw [mem_box]; push_neg
  exact ⟨j, by rw [hjeq]; omega⟩








theorem bar_armSep_of_rays (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) {a b p q : Site d}
    (hpa : (bc67_contractedLattice ω L y).Reachable a p)
    (hqb : (bc67_contractedLattice ω L y).Reachable b q)
    (hab : ¬ (bc67_contractedLattice ω L y).Reachable a b) :
    ¬ (bc67_contractedLattice ω L y).Reachable p q :=
  fun hpq => hab (hpa.trans (hpq.trans hqb.symm))












theorem bar_center_not_adj (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x z : Site d) :
    ¬ (bc67_contractedLattice ω L x).Adj x z := by
  rw [bc67_contractedLattice_adj, openSubgraph_adj]
  rintro ⟨hlat, hopen⟩
  have hxmem : x ∈ bc61_boxAround d L x := by rw [bc61_mem_boxAround]; simp
  have hclosed : removeSites (bc61_boxAround d L x) ω s(x, z) = false := by
    unfold removeSites
    rw [if_pos ⟨x, hxmem, by rw [Sym2.mem_iff]; left; rfl⟩]
  rw [hclosed] at hopen
  exact Bool.false_ne_true hopen



theorem bar_center_reach_eq (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {x z : Site d}
    (h : (bc67_contractedLattice ω L x).Reachable x z) : z = x := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj q => exact absurd hadj (bar_center_not_adj ω L x _)












theorem bar_trifForestData_of_arms_route (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hxtri : bc67_IsGnTrifurcation ω L x)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j))
    (hroute : ∀ a : Fin 3 → Site d,
      (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (a i)) →
      (∀ i, a i ∈ vertexBoundary d R) →
      ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) :
    bgc_TrifForestData ω L R := by
  classical
  
  have htip : ∀ i, ∃ t, (bc67_contractedLattice ω L x).Reachable (arm i) t ∧
      t ∈ vertexBoundary d R := by
    intro i
    obtain ⟨r, hr0, hinj, hadjr, hreachr⟩ :=
      bar_armRay_of_infiniteComponent ω L x (arm i) (harminf i)
    have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k =>
      ((bc67_contractedLattice_le ω L x) (hadjr k)).1
    have h0box : r 0 ∈ box d R := by rw [hr0]; exact harmbox i
    obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
    exact ⟨r k, hreachr k, hk⟩
  choose tip htipreach htipbdry using htip
  refine bgc_trifForestData_of_singleStar ω L R tip hxbox hxtri hsingle htipbdry ?_ ?_ ?_ ?_
  · 
    intro i hti
    have hr := htipreach i
    rw [hti] at hr
    exact harmne i (bar_center_reach_eq ω L hr.symm)
  · 
    intro i j heq
    by_contra hij
    have hrefl : (bc67_contractedLattice ω L x).Reachable (tip i) (tip j) := by
      rw [heq]
    exact bar_armSep_of_rays ω L x (htipreach i) (htipreach j) (harmsep i j hij) hrefl
  · 
    intro i j hij
    exact bar_armSep_of_rays ω L x (htipreach i) (htipreach j) (harmsep i j hij)
  · 
    exact hroute tip htipreach htipbdry










theorem bar_bk_uniqueness_of_trifData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bgc_bk_uniqueness_of_trifForest p hp1 hp0 hdata).2.1

























theorem bar_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d),
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ r : ℕ → Site d, r 0 = a ∧ Function.Injective r ∧
        (∀ k, (bc67_contractedLattice ω L y).Adj (r k) (r (k + 1)))) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b p q : Site d),
      (bc67_contractedLattice ω L y).Reachable a p →
      (bc67_contractedLattice ω L y).Reachable b q →
      ¬ (bc67_contractedLattice ω L y).Reachable a b →
      ¬ (bc67_contractedLattice ω L y).Reachable p q) ∧
    
    (∀ (r : ℕ → Site d), Function.Injective r →
      (∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1))) →
      ∀ R : ℕ, 1 ≤ R → r 0 ∈ box d R → ∃ k, r k ∈ vertexBoundary d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L y a hinf
    obtain ⟨r, hr0, hinj, hadj, -⟩ := bar_armRay_of_infiniteComponent ω L y a hinf
    exact ⟨r, hr0, hinj, hadj⟩
  · intro ω L y a b p q hpa hqb hab
    exact bar_armSep_of_rays ω L y hpa hqb hab
  · intro r hinj hadj R hR h0
    exact bar_ray_crosses_boundary r hinj hadj R hR h0

end StatMech.Walls

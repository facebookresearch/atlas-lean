/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Walls.bc55route
import Code.Percolation.BoxMergeFreeMenger
import Code.Percolation.BoxMengerAttachment
import Code.Percolation.ClusterReachesRay
import Code.Percolation.CanonicalTrifCount

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}
















def bc56_ClusterReachesNbr (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ a : Site d,
    (hypercubicLattice d).Adj 0 a ∧
    a ∈ cluster d ω x ∧
    Connected d (removeSite 0 ω) a x ∧
    (cluster d (removeSite 0 ω) x).Infinite














theorem bc56_clusterAttachment_of_reachesNbr (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc56_ClusterReachesNbr ω x) : bma_ClusterAttachment ω x := by
  classical
  obtain ⟨a, hadj, hmem, hreach, hinf⟩ := h
  have hforce : forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
    funext e; simp [forceOpenFinset]
  refine ⟨a, ∅, hadj, ?_, ?_, hmem, ?_, hinf⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · rw [hforce]; exact hreach

















def bc56_BoxClusterReachesNbr (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      bc56_ClusterReachesNbr ω x₁ ∧ bc56_ClusterReachesNbr ω x₂ ∧ bc56_ClusterReachesNbr ω x₃





theorem bc56_boxClusterAttachment_of_reachesNbr {n : ℕ}
    (h : bc56_BoxClusterReachesNbr d n) : bma_BoxClusterAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨h1, h2, h3⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨bc56_clusterAttachment_of_reachesNbr ω x₁ h1,
    bc56_clusterAttachment_of_reachesNbr ω x₂ h2,
    bc56_clusterAttachment_of_reachesNbr ω x₃ h3⟩



theorem bc56_boxMengerAttachment_of_reachesNbr {n : ℕ}
    (h : bc56_BoxClusterReachesNbr d n) : bmm_BoxMengerAttachment d n :=
  bma_boxMengerAttachment (bc56_boxClusterAttachment_of_reachesNbr h)













theorem bc56_burton_keane_bernoulli_of_reachesNbr (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p) (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc55_burton_keane_bernoulli_of_boxMenger hd p hp1 hp0
    (fun n => bc56_boxMengerAttachment_of_reachesNbr (h n))












theorem bc56_reachesNbr_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    bc56_ClusterReachesNbr ω x :=
  ⟨x, hadj, self_mem_cluster ω x, connected_rfl, hinf⟩









theorem bc56_threeRayConfig_reachesNbr_witness :
    bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) ∧
    bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px (-1)) ∧
    bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.py 1) := by
  have h0 : (CtcWitness.px 0 : Site 2) = 0 := by
    funext i; fin_cases i <;> simp [CtcWitness.px]
  have hadjpx1 : (hypercubicLattice 2).Adj 0 (CtcWitness.px 1) := by
    have := CtcWitness.px_adj 0
    rw [show (0 : ℤ) + 1 = 1 by ring] at this
    rwa [h0] at this
  have hadjpxm1 : (hypercubicLattice 2).Adj 0 (CtcWitness.px (-1)) := by
    have := CtcWitness.px_adj (-1)
    rw [show (-1 : ℤ) + 1 = 0 by ring, h0] at this
    exact this.symm
  have hadjpy1 : (hypercubicLattice 2).Adj 0 (CtcWitness.py 1) := by
    have := CtcWitness.py_adj 0
    rw [show (0 : ℤ) + 1 = 1 by ring, ← CtcWitness.px_zero_eq_py_zero, h0] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨CtcWitness.px 1, hadjpx1, self_mem_cluster _ _, connected_rfl, ?_⟩
    rw [← h0]; exact CtcWitness.cut_px_pos_infinite
  · refine ⟨CtcWitness.px (-1), hadjpxm1, self_mem_cluster _ _, connected_rfl, ?_⟩
    rw [← h0]; exact CtcWitness.cut_px_neg_infinite
  · refine ⟨CtcWitness.py 1, hadjpy1, self_mem_cluster _ _, connected_rfl, ?_⟩
    rw [← h0]; exact CtcWitness.cut_py_pos_infinite














theorem bc56_runsAlongAxis_forces_nbr_in_cluster (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    hrHD_rayPt j 1 ∈ cluster d ω x := by
  obtain ⟨L, _, hxe1, _, _⟩ := h
  rw [mem_cluster]; exact hxe1










def bc56_lp (k : ℤ) : Site 2 := ![k, 2]

theorem bc56_lp_inj : Function.Injective bc56_lp := by
  intro a b h
  have h0 : (bc56_lp a) 0 = (bc56_lp b) 0 := by rw [h]
  simpa [bc56_lp] using h0


@[simp] theorem bc56_lp_snd (k : ℤ) : (bc56_lp k) 1 = 2 := by simp [bc56_lp]

theorem bc56_lp_adj (k : ℤ) : (hypercubicLattice 2).Adj (bc56_lp k) (bc56_lp (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc56_lp]

open Classical in


noncomputable def bc56_offAxisLine : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ k : ℤ, e = s(bc56_lp k, bc56_lp (k + 1))) then true else false

theorem bc56_offAxisLine_open (k : ℤ) :
    bc56_offAxisLine s(bc56_lp k, bc56_lp (k + 1)) = true := by
  classical
  rw [bc56_offAxisLine, if_pos]; exact ⟨k, rfl⟩


theorem bc56_offAxisLine_connected_pos (m : ℤ) (hm : 0 ≤ m) :
    Connected 2 bc56_offAxisLine (bc56_lp 0) (bc56_lp m) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl _ (bc56_lp 0)
  | succ i ih =>
    have step : Connected 2 bc56_offAxisLine (bc56_lp (i : ℤ)) (bc56_lp ((i : ℤ) + 1)) :=
      IsOpenEdge.connected ⟨bc56_lp_adj (i : ℤ), bc56_offAxisLine_open (i : ℤ)⟩
    have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem bc56_lp_pos_outside_box (m : ℕ) : bc56_lp (m + 1) ∉ box 2 m := by
  rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
  simp only [bc56_lp, Matrix.cons_val_zero]
  have : ((m : ℤ) + 1).natAbs = (m + 1 : ℕ) := by omega
  omega



theorem bc56_offAxisLine_cluster_infinite :
    (cluster 2 bc56_offAxisLine (bc56_lp 0)).Infinite := by
  rw [cluster_infinite_iff]
  intro m
  exact ⟨bc56_lp (m + 1), bc56_lp_pos_outside_box m,
    bc56_offAxisLine_connected_pos ((m : ℤ) + 1) (by positivity)⟩


theorem bc56_lp_zero_mem_box : bc56_lp 0 ∈ box 2 2 := by
  rw [mem_box]; intro i; fin_cases i <;> simp [bc56_lp]




theorem bc56_offAxisLine_height_step {u v : Site 2} (_hu : u 1 = 2)
    (hadj : (openSubgraph 2 bc56_offAxisLine).Adj u v) : v 1 = 2 := by
  classical
  obtain ⟨_, hopen⟩ := hadj
  rw [bc56_offAxisLine] at hopen
  by_cases hk : ∃ k : ℤ, s(u, v) = s(bc56_lp k, bc56_lp (k + 1))
  · obtain ⟨k, hkeq⟩ := hk
    rw [Sym2.eq_iff] at hkeq
    rcases hkeq with ⟨_, hv⟩ | ⟨_, hv⟩ <;> rw [hv, bc56_lp_snd]
  · rw [if_neg hk] at hopen; exact absurd hopen (by decide)



theorem bc56_offAxisLine_height_invariant {u y : Site 2} (hu : u 1 = 2)
    (h : Connected 2 bc56_offAxisLine u y) : y 1 = 2 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (bc56_offAxisLine_height_step hu hab)






theorem bc56_offAxisLine_no_originNbr :
    ∀ a : Site 2, (hypercubicLattice 2).Adj 0 a → a ∉ cluster 2 bc56_offAxisLine (bc56_lp 0) := by
  intro a hadj hmem
  rw [mem_cluster] at hmem
  have ha2 : a 1 = 2 := bc56_offAxisLine_height_invariant (by simp [bc56_lp]) hmem
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  
  have h1 : ((0 : Site 2) 1 - a 1).natAbs = 2 := by
    simp only [Pi.zero_apply, ha2]; decide
  omega














theorem bc56_offAxisLine_no_runsAlongAxis (j : Fin 2) :
    ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j := by
  intro h
  have hmem : hrHD_rayPt j 1 ∈ cluster 2 bc56_offAxisLine (bc56_lp 0) :=
    bc56_runsAlongAxis_forces_nbr_in_cluster bc56_offAxisLine (bc56_lp 0) j h
  exact bc56_offAxisLine_no_originNbr (hrHD_rayPt j 1) (hrHD_adj_origin_rayPt_one j) hmem
















theorem bc56_status (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    ((∀ n : ℕ, bc56_BoxClusterReachesNbr d n) →
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0) ∧
    (∀ j : Fin 2, ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j) :=
  ⟨fun h => (bc56_burton_keane_bernoulli_of_reachesNbr hd p hp1 hp0 h).2.1,
   bc56_offAxisLine_no_runsAlongAxis⟩

end StatMech.Walls

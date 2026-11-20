/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.FK.CriticalPoint
import Code.FK.PcNontrivial
import Code.Lattice.CrossingParity
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanZ2
import Code.Lattice.PlanarTopology
import Code.Lattice.HypercubicLattice

open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation












noncomputable def horizWalk (c : ℤ) :
    (k : ℕ) → (a : ℤ) → (hypercubicLattice 2).Walk ![a, c] ![a + (k : ℤ), c]
  | 0, a => by
      simpa using (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk ![a, c] ![a, c])
  | k + 1, a => by
      have step : (hypercubicLattice 2).Adj ![a, c] ![a + 1, c] := latAdj_right a c
      have rest := horizWalk c k (a + 1)
      have he : (![a + 1 + (k : ℤ), c] : Site 2) = ![a + ((k + 1 : ℕ) : ℤ), c] := by
        funext i; fin_cases i <;> (simp; try ring)
      rw [he] at rest
      exact SimpleGraph.Walk.cons step rest




theorem exists_far_not_mem (S : Set (Site 2)) (hfin : S.Finite) (c a0 : ℤ) :
    ∃ N : ℤ, a0 ≤ N ∧ (![N, c] : Site 2) ∉ S := by
  by_contra h
  push Not at h
  have hsub : (fun N : ℤ => (![N, c] : Site 2)) '' (Set.Ici a0) ⊆ S := by
    rintro _ ⟨N, hN, rfl⟩; exact h N hN
  have hinj : Set.InjOn (fun N : ℤ => (![N, c] : Site 2)) (Set.Ici a0) := by
    intro x _ y _ hxy; have := congrFun hxy 0; simpa using this
  exact ((Set.Ici_infinite a0).image hinj) (hfin.subset hsub)




theorem exists_walk_exterior {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2)
    (hfin : (cluster 2 ω o).Finite) :
    ∃ z : Site 2, (hypercubicLattice 2).Reachable o z ∧ z ∉ cluster 2 ω o := by
  obtain ⟨N, hNge, hNout⟩ := exists_far_not_mem (cluster 2 ω o) hfin (o 1) (o 0)
  set k := (N - o 0).toNat with hk
  have hofun : o = ![o 0, o 1] := by funext i; fin_cases i <;> rfl
  have hkeq : (k : ℤ) = N - o 0 := by rw [hk]; omega
  refine ⟨![N, o 1], ?_, hNout⟩
  have w := horizWalk (o 1) k (o 0)
  have he : (![o 0 + (k : ℤ), o 1] : Site 2) = ![N, o 1] := by
    funext i; fin_cases i <;> (simp [hkeq]; try ring)
  rw [he] at w
  rw [hofun]
  exact ⟨w⟩





def closedCircuitEvent {u : Site 2} (c : (hypercubicLattice 2).Walk u u) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | ∀ f g : Site 2, s(f, g) ∈ c.edges → ω (sharedPrimalEdge f g) = false}














theorem exists_closed_latticeCircuit_of_finite_cluster
    {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u), c.IsCycle ∧
      ω ∈ closedCircuitEvent c := by
  obtain ⟨z, hreach, hzout⟩ := exists_walk_exterior o hfin
  obtain ⟨w⟩ := hreach
  obtain ⟨u, c0, hc0cyc⟩ := exists_dualCircuit_of_finite_cluster o hfin w hzout
  refine ⟨u, c0.mapLe (faceBoundaryGraph_le _), hc0cyc.mapLe _, ?_⟩
  intro f g hfg
  rw [Walk.edges_mapLe_eq_edges] at hfg
  have hadj : (faceBoundaryGraph (cluster 2 ω o)).Adj f g := c0.adj_of_mem_edges hfg
  have hbd : bdEdge (cluster 2 ω o) (sharedPrimalEdge f g) := hadj.2
  obtain ⟨p, q, hpq, hadjpq⟩ := sharedPrimalEdge_isLatticeEdge hadj.1
  rw [hpq] at hbd ⊢
  rw [bdEdge_mk] at hbd
  exact cluster_edgeBoundary_isClosed o ((mem_edgeBoundary).mpr ⟨hadjpq, hbd⟩)












theorem exists_enclosing_closed_latticeCircuit_of_finite_cluster
    {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ z : Site 2,
      (∃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u), c.IsCycle ∧ ω ∈ closedCircuitEvent c)
        ∧ ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z
        ∧ ∀ γ : (hypercubicLattice 2).Walk o z, ¬ Even (crossCount (cluster 2 ω o) γ) := by
  obtain ⟨z, hreach, hzout⟩ := exists_walk_exterior o hfin
  obtain ⟨w⟩ := hreach
  obtain ⟨_, hsep, hwind⟩ := cluster_enclosed_with_winding o hfin w hzout
  exact ⟨z, exists_closed_latticeCircuit_of_finite_cluster o hfin, hsep, hwind⟩









theorem finiteCluster_subset_iUnion_closedCircuit (o : Site 2) :
    {ω : ConfigSpace (Sym2 (Site 2)) | (cluster 2 ω o).Finite}
      ⊆ ⋃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u) (_ : c.IsCycle),
          closedCircuitEvent c := by
  intro ω hω
  obtain ⟨u, c, hcyc, hmem⟩ := exists_closed_latticeCircuit_of_finite_cluster o hω
  exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcyc, hmem⟩⟩⟩




theorem compl_percolationEvent_eq_finiteCluster :
    (percolationEvent 2)ᶜ
      = {ω : ConfigSpace (Sym2 (Site 2)) | (cluster 2 ω (origin 2)).Finite} := by
  ext ω
  rw [Set.mem_compl_iff, mem_percolationEvent, Set.mem_setOf_eq, Set.not_infinite]














noncomputable def fkPcUpperBound (d : ℕ) (p : ℝ) : ℝ :=
  ∑' ℓ : ℕ, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ


noncomputable def fkPcRatio (d : ℕ) (p : ℝ) : ℝ := (2 * d : ℝ) * (1 - p)

@[simp] lemma fkPcRatio_def (d : ℕ) (p : ℝ) : fkPcRatio d p = (2 * d : ℝ) * (1 - p) := rfl


lemma fkPcSummand_eq (d : ℕ) (p : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ = (ℓ : ℝ) * (fkPcRatio d p) ^ ℓ := by
  rw [fkPcRatio_def, mul_assoc, ← mul_pow]



lemma fkPcUpperBound_eq_closedForm (d : ℕ) (p : ℝ) (hx : ‖fkPcRatio d p‖ < 1) :
    fkPcUpperBound d p = (fkPcRatio d p) / (1 - fkPcRatio d p) ^ 2 := by
  unfold fkPcUpperBound
  rw [show (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ)
        = (fun ℓ : ℕ => (ℓ : ℝ) * (fkPcRatio d p) ^ ℓ) from funext (fkPcSummand_eq d p)]
  exact tsum_coe_mul_geometric_of_norm_lt_one hx


lemma fkPcRatio_tendsto_one (d : ℕ) :
    Tendsto (fun p : ℝ => fkPcRatio d p) (nhds 1) (nhds 0) := by
  have h : Tendsto (fun p : ℝ => fkPcRatio d p) (nhds 1) (nhds ((2 * d : ℝ) * (1 - 1))) := by
    unfold fkPcRatio
    exact (((tendsto_id).const_sub 1).const_mul (2 * d : ℝ))
  simpa using h


lemma fkPcClosedForm_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
  have : Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds (0 / (1 - 0) ^ 2)) := by
    apply Tendsto.div tendsto_id (Continuous.tendsto (by fun_prop) 0)
    norm_num
  simpa using this




lemma fkPcUpperBound_tendsto_one (d : ℕ) :
    Tendsto (fun p : ℝ => fkPcUpperBound d p) (nhds 1) (nhds 0) := by
  have hev : (fun p : ℝ => fkPcUpperBound d p) =ᶠ[nhds 1]
      (fun p : ℝ => (fkPcRatio d p) / (1 - fkPcRatio d p) ^ 2) := by
    have hlt : ∀ᶠ p in nhds 1, ‖fkPcRatio d p‖ < 1 := by
      have hsmall := (fkPcRatio_tendsto_one d).eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
      have hgt : ∀ᶠ p in nhds 1, (-1 : ℝ) < fkPcRatio d p :=
        (fkPcRatio_tendsto_one d).eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))
      filter_upwards [hsmall, hgt] with p hp hp'
      rw [Real.norm_eq_abs, abs_lt]; exact ⟨hp', hp⟩
    filter_upwards [hlt] with p hp
    exact fkPcUpperBound_eq_closedForm d p hp
  rw [tendsto_congr' hev]
  simpa using fkPcClosedForm_tendsto_zero.comp (fkPcRatio_tendsto_one d)





theorem exists_p_lt_one_fkPcUpperBound_lt_one (d : ℕ) :
    ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ < p → p ≤ 1 → fkPcUpperBound d p < 1 := by
  have h : ∀ᶠ p in nhds 1, fkPcUpperBound d p < 1 :=
    (fkPcUpperBound_tendsto_one d).eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hfn⟩ := h
  refine ⟨1 - ε / 2, by linarith, fun p hp1 _ => ?_⟩
  apply hfn
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith



lemma fkPcUpperBound_nonneg (d : ℕ) {p : ℝ} (hp : p ≤ 1) : 0 ≤ fkPcUpperBound d p := by
  unfold fkPcUpperBound
  apply tsum_nonneg
  intro ℓ
  have : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

























def FkNonPercolationBound (q : ℝ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : Prop :=
  1 - fkTheta 2 hp hp1 hq (q := q) ≤ fkPcUpperBound 2 p





theorem fkTheta_pos_of_nonPercolationBound {q : ℝ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hBound : FkNonPercolationBound q hp hp1 hq)
    (hsum : fkPcUpperBound 2 p < 1) :
    0 < fkTheta 2 hp hp1 hq (q := q) := by
  have h : 1 - fkTheta 2 hp hp1 hq (q := q) ≤ fkPcUpperBound 2 p := hBound
  linarith




theorem fkSubcriticalSet_bddAbove' (d : ℕ) (q : ℝ) : BddAbove (fkSubcriticalSet d q) := by
  refine ⟨1, fun x hx => ?_⟩
  obtain ⟨hp, hp1, hq, _⟩ := hx
  exact hp1.le





theorem fkSubcriticalSet_nonempty {q : ℝ} (hq : 1 ≤ q) : (fkSubcriticalSet 2 q).Nonempty := by
  set p : ℝ := 1 / (4 * 2) with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; norm_num
  have hp1 : p < 1 := by rw [hp_def]; norm_num
  have hsmall : (2 * (2 : ℕ) : ℝ) * p < 1 := by rw [hp_def]; norm_num
  exact ⟨p, hp_pos, hp1, zero_lt_one.trans_le hq,
    fkTheta_eq_zero_of_lt (by norm_num) hp_pos hp1 hq hsmall⟩



theorem not_mem_fkSubcriticalSet_of_fkTheta_pos {q : ℝ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hθ : 0 < fkTheta 2 hp hp1 hq (q := q)) : p ∉ fkSubcriticalSet 2 q := by
  intro hmem
  obtain ⟨hp', hp1', hq', hzero⟩ := hmem
  
  rw [show hp' = hp from rfl, show hp1' = hp1 from rfl, show hq' = hq from rfl] at hzero
  exact (ne_of_gt hθ) hzero




















theorem fkPc_lt_one {q : ℝ} (hq : 1 ≤ q)
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p →
        FkNonPercolationBound q hp hp1 (zero_lt_one.trans_le hq)) :
    fkPc 2 q < 1 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨p₁, hp₁lt, hp₁bound⟩ := exists_p_lt_one_fkPcUpperBound_lt_one 2
  obtain ⟨p₂, hp₂lt, hp₂geom⟩ := hGeom
  
  set t : ℝ := max (max p₁ p₂) 0 with ht
  have htlt : t < 1 := max_lt (max_lt hp₁lt hp₂lt) (by norm_num)
  have ht0 : (0 : ℝ) ≤ t := le_max_right _ _
  have hp₁t : p₁ ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have hp₂t : p₂ ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
  
  set s : ℝ := (t + 1) / 2 with hs
  have hts : t < s := by rw [hs]; linarith
  have hslt : s < 1 := by rw [hs]; linarith
  have hs0 : (0 : ℝ) < s := by rw [hs]; linarith
  
  have hub : ∀ r ∈ fkSubcriticalSet 2 q, r ≤ s := by
    intro r hr
    by_contra hcon
    push Not at hcon
    obtain ⟨hr0, hr1, _, hzero⟩ := hr
    
    have hp₁r : p₁ < r := lt_of_le_of_lt (le_trans hp₁t hts.le) hcon
    have hp₂r : p₂ < r := lt_of_le_of_lt (le_trans hp₂t hts.le) hcon
    have hbnd : fkPcUpperBound 2 r < 1 := hp₁bound r hp₁r hr1.le
    have hcb : FkNonPercolationBound q hr0 hr1 hq0 := hp₂geom r hr0 hr1 hp₂r
    have hθ : 0 < fkTheta 2 hr0 hr1 hq0 (q := q) :=
      fkTheta_pos_of_nonPercolationBound hr0 hr1 hq0 hcb hbnd
    exact not_mem_fkSubcriticalSet_of_fkTheta_pos hr0 hr1 hq0 hθ
      ⟨hr0, hr1, hq0, hzero⟩
  
  calc fkPc 2 q = sSup (fkSubcriticalSet 2 q) := rfl
    _ ≤ s := csSup_le (fkSubcriticalSet_nonempty hq) hub
    _ < 1 := hslt





theorem fkPc_pos_and_lt_one {q : ℝ} (hq : 1 ≤ q)
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p →
        FkNonPercolationBound q hp hp1 (zero_lt_one.trans_le hq)) :
    0 < fkPc 2 q ∧ fkPc 2 q < 1 :=
  ⟨fkPc_pos_of_two_le (le_refl 2) hq, fkPc_lt_one hq hGeom⟩

end FK

end StatMech

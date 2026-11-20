/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Percolation.GridBoxConnected
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.CanonicalTrifCount
import Code.Walls.bc21trifurc

open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}



theorem bc24_cluster_ne_of_not_connected {σ : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (h : ¬ Connected d σ a b) : cluster d σ a ≠ cluster d σ b := by
  intro heq
  exact h (mem_cluster.mp (heq ▸ self_mem_cluster σ b))












theorem bc24_box_merges_infinite {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    cluster d (forceOpenFinset (boxEdges d n) ω) x
      = cluster d (forceOpenFinset (boxEdges d n) ω) y :=
  box_allOpen_cluster_eq ω hx hy













theorem bc24_arm_connected_box {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {a b z : Site d} (hb : b ∈ box d n) (hz : z ∈ box d n)
    (hab : Connected d ω a b) :
    Connected d (forceOpenFinset (boxEdges d n) ω) a z := by
  
  have hab' : Connected d (forceOpenFinset (boxEdges d n) ω) a b :=
    connected_mono (forceOpenFinset_le _ ω) hab
  
  exact hab'.trans (box_allOpen_connected ω hb hz)






theorem bc24_armEnds_connected_through_box {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
    (hb₁ : b₁ ∈ box d n) (hb₂ : b₂ ∈ box d n) (hb₃ : b₃ ∈ box d n)
    (h₁ : Connected d ω a₁ b₁) (h₂ : Connected d ω a₂ b₂) (h₃ : Connected d ω a₃ b₃) :
    Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₂ ∧
      Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₃ ∧
      Connected d (forceOpenFinset (boxEdges d n) ω) a₂ a₃ := by
  
  have c1 : Connected d (forceOpenFinset (boxEdges d n) ω) a₁ b₁ :=
    bc24_arm_connected_box ω hb₁ hb₁ h₁
  have c2 : Connected d (forceOpenFinset (boxEdges d n) ω) a₂ b₁ :=
    bc24_arm_connected_box ω hb₂ hb₁ h₂
  have c3 : Connected d (forceOpenFinset (boxEdges d n) ω) a₃ b₁ :=
    bc24_arm_connected_box ω hb₃ hb₁ h₃
  exact ⟨c1.trans c2.symm, c1.trans c3.symm, c2.trans c3.symm⟩
























def IsCoarseTrifurcation (d n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (b₁ ∈ box d n ∧ b₂ ∈ box d n ∧ b₃ ∈ box d n) ∧
    ((hypercubicLattice d).Adj a₁ b₁ ∧ (hypercubicLattice d).Adj a₂ b₂ ∧
      (hypercubicLattice d).Adj a₃ b₃) ∧
    (Connected d ω a₁ b₁ ∧ Connected d ω a₂ b₂ ∧ Connected d ω a₃ b₃) ∧
    ((cluster d (removeSites (boxFinsetBK d n) ω) a₁).Infinite ∧
      (cluster d (removeSites (boxFinsetBK d n) ω) a₂).Infinite ∧
      (cluster d (removeSites (boxFinsetBK d n) ω) a₃).Infinite) ∧
    (¬ Connected d (removeSites (boxFinsetBK d n) ω) a₁ a₂ ∧
      ¬ Connected d (removeSites (boxFinsetBK d n) ω) a₁ a₃ ∧
      ¬ Connected d (removeSites (boxFinsetBK d n) ω) a₂ a₃)






theorem bc24_coarseTrif_armClusters_distinct_after_boxRemoval {n : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} (h : IsCoarseTrifurcation d n ω) :
    ∃ a₁ a₂ a₃ : Site d,
      (cluster d (removeSites (boxFinsetBK d n) ω) a₁).Infinite ∧
      (cluster d (removeSites (boxFinsetBK d n) ω) a₂).Infinite ∧
      (cluster d (removeSites (boxFinsetBK d n) ω) a₃).Infinite ∧
      cluster d (removeSites (boxFinsetBK d n) ω) a₁
          ≠ cluster d (removeSites (boxFinsetBK d n) ω) a₂ ∧
      cluster d (removeSites (boxFinsetBK d n) ω) a₁
          ≠ cluster d (removeSites (boxFinsetBK d n) ω) a₃ ∧
      cluster d (removeSites (boxFinsetBK d n) ω) a₂
          ≠ cluster d (removeSites (boxFinsetBK d n) ω) a₃ := by
  obtain ⟨a₁, a₂, a₃, _b₁, _b₂, _b₃, _hne, _hbox, _hadj, _hconn, hinf, hsep⟩ := h
  exact ⟨a₁, a₂, a₃, hinf.1, hinf.2.1, hinf.2.2,
    bc24_cluster_ne_of_not_connected hsep.1,
    bc24_cluster_ne_of_not_connected hsep.2.1,
    bc24_cluster_ne_of_not_connected hsep.2.2⟩







theorem bc24_box_hub_routes_armEnds {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    (h : IsCoarseTrifurcation d n ω) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₂ ∧
      Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₃ ∧
      Connected d (forceOpenFinset (boxEdges d n) ω) a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hne, hbox, _hadj, hconn, _hinf, _hsep⟩ := h
  obtain ⟨r12, r13, r23⟩ :=
    bc24_armEnds_connected_through_box ω hbox.1 hbox.2.1 hbox.2.2
      hconn.1 hconn.2.1 hconn.2.2
  exact ⟨a₁, a₂, a₃, hne, r12, r13, r23⟩










theorem bc24_box_zero (d : ℕ) : box d 0 = {(0 : Site d)} := by
  ext x
  simp only [mem_box, Set.mem_singleton_iff]
  constructor
  · intro hx; funext i; have hi := hx i; simp only [Pi.zero_apply]; omega
  · rintro rfl i; simp


theorem bc24_zero_mem_boxFinsetBK (d : ℕ) : (0 : Site d) ∈ boxFinsetBK d 0 := by
  simp only [boxFinsetBK, Set.Finite.mem_toFinset]
  intro i; simp




theorem bc24_removeSites_box_zero (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (boxFinsetBK d 0) ω = removeSite (0 : Site d) ω := by
  funext e
  unfold removeSites removeSite
  by_cases h0 : (0 : Site d) ∈ e
  · have hex : ∃ t ∈ boxFinsetBK d 0, t ∈ e := ⟨0, bc24_zero_mem_boxFinsetBK d, h0⟩
    simp [hex, h0]
  · have hnex : ¬ ∃ t ∈ boxFinsetBK d 0, t ∈ e := by
      rintro ⟨t, ht, hte⟩
      have ht0 : t = (0 : Site d) := by
        have : t ∈ box d 0 := by simpa [boxFinsetBK, Set.Finite.mem_toFinset] using ht
        rw [bc24_box_zero] at this; simpa using this
      exact h0 (ht0 ▸ hte)
    simp [hnex, h0]







theorem bc24_coarseTrif_of_canonical_origin {ω : ConfigSpace (Sym2 (Site d))}
    (h : IsCanonicalTrifurcation d ω (0 : Site d)) :
    IsCoarseTrifurcation d 0 ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := h
  have hbox0 : (0 : Site d) ∈ box d 0 := by intro i; simp
  
  have hc₁ : Connected d ω a₁ (0 : Site d) :=
    (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj.1).symm
  have hc₂ : Connected d ω a₂ (0 : Site d) :=
    (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj.2.1).symm
  have hc₃ : Connected d ω a₃ (0 : Site d) :=
    (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj.2.2).symm
  
  have hla₁ : (hypercubicLattice d).Adj a₁ (0 : Site d) :=
    ((openSubgraph_le ω) hadj.1).symm
  have hla₂ : (hypercubicLattice d).Adj a₂ (0 : Site d) :=
    ((openSubgraph_le ω) hadj.2.1).symm
  have hla₃ : (hypercubicLattice d).Adj a₃ (0 : Site d) :=
    ((openSubgraph_le ω) hadj.2.2).symm
  
  
  have hbridge := bc24_removeSites_box_zero (d := d) ω
  refine ⟨a₁, a₂, a₃, 0, 0, 0, hne, ⟨hbox0, hbox0, hbox0⟩,
    ⟨hla₁, hla₂, hla₃⟩, ⟨hc₁, hc₂, hc₃⟩, ?_, ?_⟩
  · rw [hbridge]; exact hinf
  · rw [hbridge]; exact hsep





theorem bc24_coarseTrif_nonvacuous :
    ∃ ω : ConfigSpace (Sym2 (Site 2)), IsCoarseTrifurcation 2 0 ω :=
  ⟨StatMech.Percolation.CtcWitness.threeRayConfig,
    bc24_coarseTrif_of_canonical_origin bc21_threeRay_trif_at_origin⟩

end StatMech.Walls

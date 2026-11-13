/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Percolation.CorridorConfinement
import Code.Percolation.HrouteHighDim

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}









theorem bka_far_witness (ω : ConfigSpace (Sym2 (Site d))) (w : Site d)
    (hinf : (cluster d ω w).Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d ω w y :=
  (cluster_infinite_iff ω w).mp hinf n



theorem bka_exists_far_connected (ω : ConfigSpace (Sym2 (Site d))) (w : Site d)
    (hinf : (cluster d ω w).Infinite) (n : ℕ) :
    ∃ y ∈ cluster d ω w, y ∉ box d n := by
  obtain ⟨y, hyb, hyc⟩ := bka_far_witness ω w hinf n
  exact ⟨y, hyc, hyb⟩










theorem bka_isOpenEdge_survives (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (hopen : IsOpenEdge d ω x y) (h0 : (0 : Site d) ∉ s(x, y)) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y := by
  obtain ⟨hadj, hval⟩ := hopen
  refine ⟨hadj, ?_⟩
  rw [removeSite_apply_of_notMem h0]
  
  have hle := forceOpenFinset_le G ω
  have := hle s(x, y)
  rw [hval] at this
  exact le_antisymm (by simp) this










theorem bka_axis_corridor_step (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges j L))
      (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) :=
  bcc_axisCorridor_corridorStep j L hL




theorem bka_three_independent_axis_neighbours {j₁ j₂ j₃ : Fin d}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) :
    (hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₂ 1 ∧ hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₃ 1 ∧
      hrHD_rayPt j₂ 1 ≠ hrHD_rayPt j₃ 1) ∧
    ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧
      (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧
      (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₂ t) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₃ t) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₂ s ≠ hrHD_rayPt j₃ t) :=
  ⟨⟨hrHD_rayPt_one_ne_of_ne h12, hrHD_rayPt_one_ne_of_ne h13, hrHD_rayPt_one_ne_of_ne h23⟩,
    ⟨hrHD_adj_origin_rayPt_one j₁, hrHD_adj_origin_rayPt_one j₂, hrHD_adj_origin_rayPt_one j₃⟩,
    fun _ _ hs => hrHD_rayPt_disjoint_of_ne h12 hs,
    fun _ _ hs => hrHD_rayPt_disjoint_of_ne h13 hs,
    fun _ _ hs => hrHD_rayPt_disjoint_of_ne h23 hs⟩


















def bka_MergeFree (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite) ∧
    (cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃)









theorem bka_forceOpenFinset_empty (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
  funext e; simp [forceOpenFinset]


theorem bka_corridor_refl (G : Finset (Sym2 (Site d))) (a : Site d) :
    Relation.ReflTransGen (CorridorStep G) a a := Relation.ReflTransGen.refl













theorem bka_distinct_clusters (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_MergeFree ω) : bcc_distinct_clusters_residue ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := h
  refine ⟨a₁, a₂, a₃, ∅, a₁, a₂, a₃, hne, hadj,
    ⟨bka_corridor_refl ∅ a₁, bka_corridor_refl ∅ a₂, bka_corridor_refl ∅ a₃⟩, ?_, ?_⟩
  · 
    rw [bka_forceOpenFinset_empty]
    exact ⟨hi1, hi2, hi3⟩
  · rw [bka_forceOpenFinset_empty]
    exact ⟨hd12, hd13, hd23⟩





theorem bka_disjointRouting_of_mergeFree (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_MergeFree ω) : DisjointCorridorRouting ω :=
  bcc_disjointRouting_of_residue ω (bka_distinct_clusters ω h)




















theorem bka_routing_of_mergeFree (n : ℕ)
    (hmf : ∀ ω ∈ threeMeetBox d n, bka_MergeFree ω) :
    hrHD_DisjointRouting d n := by
  classical
  intro ω hω
  obtain ⟨a₁, a₂, a₃, hne, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := hmf ω hω
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  refine ⟨F, a₁, a₂, a₃, ?_⟩
  
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h <;> (rw [h]; exact Sym2.mem_mk_left _ _)
  have hrm : removeSite (0:Site d) (forceOpenFinset F ω) = removeSite (0:Site d) ω :=
    removeSite_forceOpen_eq 0 F hFmem ω
  
  refine ⟨hne, hadj, ?_, ?_, ?_, ?_⟩
  · rw [hrm]; exact ⟨hi1, hi2, hi3⟩
  · rw [hrm]; intro hc; exact hd12 (cluster_eq_of_connected hc)
  · rw [hrm]; intro hc; exact hd13 (cluster_eq_of_connected hc)
  · rw [hrm]; intro hc; exact hd23 (cluster_eq_of_connected hc)












theorem bka_rhoOpenEdge_decompose (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {u v : Site d}
    (hadj : (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v) :
    (hypercubicLattice d).Adj u v ∧ (0 : Site d) ∉ s(u, v) ∧
      (IsOpenEdge d ω u v ∨ s(u, v) ∈ G) := by
  rw [openSubgraph_adj] at hadj
  obtain ⟨hlat, hval⟩ := hadj
  have h0 : (0 : Site d) ∉ s(u, v) := by
    intro hmem; rw [removeSite_apply_of_mem hmem] at hval; exact absurd hval (by simp)
  rw [removeSite_apply_of_notMem h0] at hval
  refine ⟨hlat, h0, ?_⟩
  by_cases hg : s(u, v) ∈ G
  · exact Or.inr hg
  · rw [forceOpenFinset_of_notMem hg] at hval; exact Or.inl ⟨hlat, hval⟩




theorem bka_no_crossing_edge (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hne : cluster d ω x ≠ cluster d ω y) {u v : Site d}
    (hu : u ∈ cluster d ω x) (hv : v ∈ cluster d ω y) (hedge : IsOpenEdge d ω u v) :
    False := by
  rw [mem_cluster] at hu hv
  exact hne (cluster_eq_of_connected (hu.trans (hedge.connected.trans hv.symm)))









theorem bka_region_rhoAdjClosed (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (R : Set (Site d))
    (homega : ∀ u v, u ∈ R → IsOpenEdge d ω u v → v ∈ R)
    (hG : ∀ u v, u ∈ R → s(u, v) ∈ G → v ∈ R) :
    ∀ u v, u ∈ R →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ R := by
  intro u v hu hadj
  obtain ⟨_, _, hcase⟩ := bka_rhoOpenEdge_decompose ω G hadj
  rcases hcase with hopen | hg
  · exact homega u v hu hopen
  · exact hG u v hu hg

















def bka_ClusterRespectingRouting (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) (w₁ w₂ w₃ : Site d)
    (R₁ R₂ R₃ : Set (Site d)),
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    (Relation.ReflTransGen (CorridorStep G) a₁ w₁ ∧
      Relation.ReflTransGen (CorridorStep G) a₂ w₂ ∧
      Relation.ReflTransGen (CorridorStep G) a₃ w₃) ∧
    ((cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite) ∧
    (a₁ ∈ R₁ ∧ a₂ ∈ R₂ ∧ a₃ ∈ R₃) ∧
    ((∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁) ∧
      (∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂) ∧
      (∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)) ∧
    ((∀ u v, u ∈ R₁ → s(u, v) ∈ G → v ∈ R₁) ∧
      (∀ u v, u ∈ R₂ → s(u, v) ∈ G → v ∈ R₂) ∧
      (∀ u v, u ∈ R₃ → s(u, v) ∈ G → v ∈ R₃)) ∧
    (Disjoint R₁ R₂ ∧ Disjoint R₁ R₃ ∧ Disjoint R₂ R₃)






theorem bka_distinct_clusters_of_clusterRespecting (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_ClusterRespectingRouting ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, R₁, R₂, R₃, hne, hadj, ⟨hc1, hc2, hc3⟩,
    ⟨hw1, hw2, hw3⟩, ⟨hm1, hm2, hm3⟩, ⟨ho1, ho2, ho3⟩, ⟨hg1, hg2, hg3⟩,
    hd12, hd13, hd23⟩ := h
  
  refine ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, R₁, R₂, R₃, hne, hadj, ⟨hc1, hc2, hc3⟩,
    ⟨hw1, hw2, hw3⟩, ⟨hm1, hm2, hm3⟩,
    ⟨bka_region_rhoAdjClosed ω G R₁ ho1 hg1, bka_region_rhoAdjClosed ω G R₂ ho2 hg2,
      bka_region_rhoAdjClosed ω G R₃ ho3 hg3⟩, hd12, hd13, hd23⟩
















def bka_CorridorConfinement (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  DisjointCorridorRouting ω






theorem bka_disjointRouting_of_corridorConfinement (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_CorridorConfinement ω) : DisjointCorridorRouting ω := h





theorem bka_distinct_clusters_of_corridorConfinement (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_CorridorConfinement ω) : bcc_distinct_clusters_residue ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, S₁, S₂, S₃, hne, hadj, ⟨hc1, hc2, hc3⟩,
    ⟨hw1, hw2, hw3⟩, ⟨hm1, hm2, hm3⟩, ⟨hcl1, hcl2, hcl3⟩, hd12, hd13, hd23⟩ := h
  set ϱ := removeSite 0 (forceOpenFinset G ω) with hϱ
  
  
  have hdist : cluster d ϱ a₁ ≠ cluster d ϱ a₂ ∧ cluster d ϱ a₁ ≠ cluster d ϱ a₃ ∧
      cluster d ϱ a₂ ≠ cluster d ϱ a₃ :=
    (bcc_disjoint_sides_iff_clusters_distinct ϱ a₁ a₂ a₃).mp
      ⟨S₁, S₂, S₃, ⟨hm1, hm2, hm3⟩, ⟨hcl1, hcl2, hcl3⟩, hd12, hd13, hd23⟩
  exact ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩, hdist⟩















theorem bka_residue_iff_corridorConfinement (ω : ConfigSpace (Sym2 (Site d))) :
    bcc_distinct_clusters_residue ω ↔ bka_CorridorConfinement ω := by
  constructor
  · intro h; exact bcc_disjointRouting_of_residue ω h
  · intro h; exact bka_distinct_clusters_of_corridorConfinement ω h

end Percolation

end StatMech

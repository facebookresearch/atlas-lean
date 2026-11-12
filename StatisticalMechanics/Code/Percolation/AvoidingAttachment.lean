/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Percolation.ClusterAttachment

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










theorem ava_support_mem_cluster (ω : ConfigSpace (Sym2 (Site d))) {a x z : Site d}
    (w : (openSubgraph d ω).Walk a x) (hz : z ∈ w.support) :
    z ∈ cluster d ω x := by
  have hza : Connected d ω a z := (w.takeUntil z hz).reachable
  rw [mem_cluster]
  exact (Connected.symm w.reachable).trans hza




theorem ava_origin_notMem_support_of_notMem_cluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (w : (openSubgraph d ω).Walk a x)
    (h0 : (0 : Site d) ∉ cluster d ω x) :
    (0 : Site d) ∉ w.support :=
  fun hmem => h0 (ava_support_mem_cluster ω w hmem)










theorem ava_removeSite_openSubgraph_le (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (removeSite 0 ω) ≤ openSubgraph d ω := by
  intro x y h
  obtain ⟨hadj, hval⟩ := h
  refine ⟨hadj, ?_⟩
  by_cases h0 : (0 : Site d) ∈ s(x, y)
  · rw [removeSite_apply_of_mem h0] at hval; exact absurd hval (by simp)
  · rwa [removeSite_apply_of_notMem h0] at hval



theorem ava_origin_no_adj_removeSite (ω : ConfigSpace (Sym2 (Site d))) (y : Site d) :
    ¬ (openSubgraph d (removeSite 0 ω)).Adj (0 : Site d) y := by
  rintro ⟨hadj, hval⟩
  have h0 : (0 : Site d) ∈ s((0 : Site d), y) := Sym2.mem_mk_left _ _
  rw [removeSite_apply_of_mem h0] at hval
  exact absurd hval (by simp)




theorem ava_connected_origin_eq (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (h : Connected d (removeSite 0 ω) (0 : Site d) x) : x = 0 := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj p => exact absurd hadj (ava_origin_no_adj_removeSite ω _)




theorem ava_origin_notMem_cluster_removeSite (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hx : x ≠ 0) : (0 : Site d) ∉ cluster d (removeSite 0 ω) x := by
  rw [mem_cluster]
  intro h
  exact hx (ava_connected_origin_eq ω h.symm)













theorem ava_avoiding_walk_of_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hx : x ≠ 0) (hc : Connected d (removeSite 0 ω) a x) :
    ∃ w : (openSubgraph d ω).Walk a x, (0 : Site d) ∉ w.support := by
  obtain ⟨wr⟩ := hc
  refine ⟨wr.mapLe (ava_removeSite_openSubgraph_le ω), ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro hmem
  exact ava_origin_notMem_cluster_removeSite ω hx
    (ava_support_mem_cluster (removeSite 0 ω) wr hmem)



theorem ava_connected_of_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hc : Connected d (removeSite 0 ω) a x) : Connected d ω a x :=
  hc.mono (ava_removeSite_openSubgraph_le ω)














def ava_AvoidingRoutingResidue (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  x ≠ 0 ∧ (cluster d (removeSite 0 ω) x).Infinite ∧
    ∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d (removeSite 0 ω) x





theorem ava_avoidingAttachment_of_removeSiteCluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (hx : x ≠ 0) (hadj : (hypercubicLattice d).Adj 0 a)
    (hmemR : a ∈ cluster d (removeSite 0 ω) x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  have hc : Connected d (removeSite 0 ω) a x := (mem_cluster.mp hmemR).symm
  have hmem : a ∈ cluster d ω x := by
    rw [mem_cluster]; exact ava_connected_of_removeSite ω (mem_cluster.mp hmemR)
  obtain ⟨w, hw⟩ := ava_avoiding_walk_of_removeSite ω hx hc
  exact ⟨a, w, hadj, hmem, hw, hri⟩



theorem ava_avoidingAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : ava_AvoidingRoutingResidue ω x) : cla_AvoidingAttachment ω x := by
  obtain ⟨hx, hri, a, hadj, hmemR⟩ := h
  exact ava_avoidingAttachment_of_removeSiteCluster ω hx hadj hmemR hri




theorem ava_clusterAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : ava_AvoidingRoutingResidue ω x) : bma_ClusterAttachment ω x :=
  cla_clusterAttachment_of_avoidingAttachment ω x (ava_avoidingAttachment ω x h)













theorem ava_avoidingAttachment_of_notMemCluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (hadj : (hypercubicLattice d).Adj 0 a) (hmem : a ∈ cluster d ω x)
    (h0 : (0 : Site d) ∉ cluster d ω x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  obtain ⟨w⟩ := (mem_cluster.mp hmem).symm
  exact ⟨a, w, hadj, hmem, ava_origin_notMem_support_of_notMem_cluster ω w h0, hri⟩











theorem ava_avoidingRoutingResidue_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    ava_AvoidingRoutingResidue ω x :=
  ⟨hadj.ne.symm, hri, x, hadj, self_mem_cluster (removeSite 0 ω) x⟩



theorem ava_avoidingAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x :=
  ava_avoidingAttachment ω x (ava_avoidingRoutingResidue_of_neighbour ω x hadj hri)













def ava_BoxAvoidingRoutingResidue (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
        ava_AvoidingRoutingResidue ω x₃



theorem ava_boxAvoidingAttachment_of_boxResidue {n : ℕ}
    (h : ava_BoxAvoidingRoutingResidue d n) : cla_BoxAvoidingAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨h1, h2, h3⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨ava_avoidingAttachment ω x₁ h1, ava_avoidingAttachment ω x₂ h2,
    ava_avoidingAttachment ω x₃ h3⟩




theorem ava_disjointRouting_of_boxResidue {n : ℕ}
    (h : ava_BoxAvoidingRoutingResidue d n) : hrHD_DisjointRouting d n :=
  cla_disjointRouting_of_boxAvoiding (ava_boxAvoidingAttachment_of_boxResidue h)











theorem ava_three_residues_of_neighbours (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
      ava_AvoidingRoutingResidue ω x₃ :=
  ⟨ava_avoidingRoutingResidue_of_neighbour ω x₁ hadj.1 hri.1,
    ava_avoidingRoutingResidue_of_neighbour ω x₂ hadj.2.1 hri.2.1,
    ava_avoidingRoutingResidue_of_neighbour ω x₃ hadj.2.2 hri.2.2⟩

end Percolation

end StatMech

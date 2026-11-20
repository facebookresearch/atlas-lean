/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeaneUniqueness

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}











theorem bc9nbr_adj_survives_origin_cut (ω : ConfigSpace (Sym2 (Site d))) {u w : Site d}
    (hu : u ≠ 0) (hw : w ≠ 0) (hadj : (openSubgraph d ω).Adj u w) :
    (openSubgraph d (removeSite 0 ω)).Adj u w := by
  rw [openSubgraph_adj] at hadj ⊢
  refine ⟨hadj.1, ?_⟩
  have h0not : (0 : Site d) ∉ s(u, w) := by
    rw [Sym2.mem_iff, not_or]
    exact ⟨fun h => hu h.symm, fun h => hw h.symm⟩
  rw [removeSite_apply_of_notMem h0not]
  exact hadj.2





theorem bc9nbr_adj_dies_origin_cut (ω : ConfigSpace (Sym2 (Site d))) {u w : Site d}
    (h0 : (0 : Site d) ∈ s(u, w)) :
    ¬ (openSubgraph d (removeSite 0 ω)).Adj u w := by
  rw [openSubgraph_adj]
  rw [removeSite_apply_of_mem h0]
  simp













theorem bc9nbr_avoiding_walk_survives_origin_cut (ω : ConfigSpace (Sym2 (Site d))) {u w : Site d}
    (p : (openSubgraph d ω).Walk u w) (hp : (0 : Site d) ∉ p.support) :
    Connected d (removeSite 0 ω) u w := by
  induction p with
  | nil => exact connected_rfl
  | @cons a b c hadj p' ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hp
    obtain ⟨h0a, h0rest⟩ := hp
    
    have h0b : (0 : Site d) ≠ b := fun h => h0rest (h ▸ p'.start_mem_support)
    have hstep : (openSubgraph d (removeSite 0 ω)).Adj a b :=
      bc9nbr_adj_survives_origin_cut ω (Ne.symm h0a) (Ne.symm h0b) hadj
    exact (SimpleGraph.Adj.reachable hstep).trans (ih h0rest)


















theorem bc9nbr_origin_neighbour_of_connected (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (hy0 : y ≠ 0) (hconn : Connected d ω 0 y) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧
      ∃ r : (openSubgraph d ω).Walk n y, (0 : Site d) ∉ r.support := by
  
  obtain ⟨p⟩ := hconn.symm
  have h0mem : (0 : Site d) ∈ p.support := p.end_mem_support
  
  set p' := p.takeUntil 0 h0mem with hp'def
  have hcount : p'.support.count (0 : Site d) = 1 := p.count_support_takeUntil_eq_one h0mem
  
  have hqcount : (p'.reverse).support.count (0 : Site d) = 1 := by
    rw [SimpleGraph.Walk.support_reverse, List.count_reverse]; exact hcount
  
  cases hq : p'.reverse with
  | nil => exact absurd rfl hy0
  | @cons _ n _ hadj r =>
    refine ⟨n, hadj, r, ?_⟩
    
    rw [hq, SimpleGraph.Walk.support_cons, List.count_cons] at hqcount
    simp only [beq_iff_eq] at hqcount
    have hr0 : r.support.count (0 : Site d) = 0 := by simpa using hqcount
    exact List.count_eq_zero.mp hr0










theorem bc9nbr_mem_neighbour_cutCluster (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (hy0 : y ≠ 0) (hconn : Connected d ω 0 y) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧ y ∈ cluster d (removeSite 0 ω) n := by
  obtain ⟨n, hadj, r, hr⟩ := bc9nbr_origin_neighbour_of_connected ω hy0 hconn
  exact ⟨n, hadj, mem_cluster.mpr (bc9nbr_avoiding_walk_survives_origin_cut ω r hr)⟩



theorem bc9nbr_mem_neighbour_cutCluster' (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (hy0 : y ≠ 0) (hconn : Connected d ω y 0) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧ y ∈ cluster d (removeSite 0 ω) n :=
  bc9nbr_mem_neighbour_cutCluster ω hy0 hconn.symm










theorem bc9nbr_mem_neighbour_cutCluster_strong (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (hy0 : y ≠ 0) (hconn : Connected d ω 0 y) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧ Connected d (removeSite 0 ω) n y ∧
      y ∈ cluster d (removeSite 0 ω) n := by
  obtain ⟨n, hadj, r, hr⟩ := bc9nbr_origin_neighbour_of_connected ω hy0 hconn
  have hsurv : Connected d (removeSite 0 ω) n y :=
    bc9nbr_avoiding_walk_survives_origin_cut ω r hr
  exact ⟨n, hadj, hsurv, mem_cluster.mpr hsurv⟩











theorem bc9nbr_mem_neighbour_cutCluster_of_adj (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (hy0 : y ≠ 0) (hadj : (openSubgraph d ω).Adj 0 y) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧ y ∈ cluster d (removeSite 0 ω) n :=
  bc9nbr_mem_neighbour_cutCluster ω hy0 hadj.reachable



section AxiomAudit


#guard_msgs in
#print axioms bc9nbr_adj_survives_origin_cut


#guard_msgs in
#print axioms bc9nbr_avoiding_walk_survives_origin_cut


#guard_msgs in
#print axioms bc9nbr_origin_neighbour_of_connected


#guard_msgs in
#print axioms bc9nbr_mem_neighbour_cutCluster


#guard_msgs in
#print axioms bc9nbr_mem_neighbour_cutCluster_strong

end AxiomAudit

end Walls

end StatMech

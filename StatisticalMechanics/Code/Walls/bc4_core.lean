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
import Code.Walls.bc4_avoidingsurvives
import Code.Walls.bc4_nbrfinite
import Code.Walls.bc4_pigeonhole
import Code.Walls.bc3_distinctwitnessclusters

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}


















theorem bc4c_origin_neighbour_of_connected (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
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






theorem bc4c_mem_neighbour_cutCluster (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (hy0 : y ≠ 0) (hconn : Connected d ω 0 y) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧ y ∈ cluster d (removeSite 0 ω) n := by
  obtain ⟨n, hadj, r, hr⟩ := bc4c_origin_neighbour_of_connected ω hy0 hconn
  exact ⟨n, hadj, bc4_cluster_mono_of_avoiding ω r hr⟩










theorem bc4c_punctured_cluster_subset_neighbour_cutClusters (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (h0mem : (0 : Site d) ∈ cluster d ω x) :
    (cluster d ω x \ {(0 : Site d)})
      ⊆ ⋃ n ∈ {n | (openSubgraph d ω).Adj 0 n}, cluster d (removeSite 0 ω) n := by
  have hx0 : cluster d ω x = cluster d ω 0 := cluster_eq_of_connected (mem_cluster.mp h0mem)
  intro y hy
  obtain ⟨hyc, hy0⟩ := hy
  simp only [Set.mem_singleton_iff] at hy0
  rw [hx0, mem_cluster] at hyc
  obtain ⟨n, hadj, hmem⟩ := bc4c_mem_neighbour_cutCluster ω hy0 hyc
  exact Set.mem_biUnion (by exact hadj) hmem













theorem bc4c_originCutLeavesInfinite (ω : ConfigSpace (Sym2 (Site d))) :
    bc3_OriginCutLeavesInfinite ω := by
  intro x hinf h0mem
  have hx0 : cluster d ω x = cluster d ω 0 := cluster_eq_of_connected (mem_cluster.mp h0mem)
  
  have hdiff : (cluster d ω x \ {(0 : Site d)}).Infinite :=
    hinf.diff (Set.finite_singleton _)
  
  have hNfin : {n : Site d | (openSubgraph d ω).Adj 0 n}.Finite :=
    bc4_origin_openNeighbours_finite ω
  
  have hUinf :
      (⋃ n ∈ {n : Site d | (openSubgraph d ω).Adj 0 n}, cluster d (removeSite 0 ω) n).Infinite :=
    hdiff.mono (bc4c_punctured_cluster_subset_neighbour_cutClusters ω h0mem)
  
  obtain ⟨n, hnN, hninf⟩ := bc4_finite_biUnion_infinite hNfin hUinf
  refine ⟨n, ?_, hninf⟩
  
  rw [hx0, mem_cluster]
  have hadj0n : (openSubgraph d ω).Adj 0 n := hnN
  exact hadj0n.reachable










theorem bc4c_threeArms_cutInfinite (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite) :
    ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
      x₃' ∈ cluster d ω x₃ ∧
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite :=
  bc3_threeArms_cutInfinite_of_residue ω (bc4c_originCutLeavesInfinite ω) hi1 hi2 hi3





theorem bc4c_distinctWitnessClusters (n : ℕ) : bc3_DistinctWitnessClusters d n :=
  bc3_distinctWitnessClusters n (fun ω _ => bc4c_originCutLeavesInfinite ω)










theorem bc4c_arm_cutInfinite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d ω x).Infinite) :
    ∃ x', x' ∈ cluster d ω x ∧ (cluster d (removeSite 0 ω) x').Infinite :=
  bc3_arm_cutInfinite_of_residue ω (bc4c_originCutLeavesInfinite ω) x hinf




theorem bc4c_closes_residue (ω : ConfigSpace (Sym2 (Site d))) :
    bc3_OriginCutLeavesInfinite ω :=
  bc4c_originCutLeavesInfinite ω

end Walls

end StatMech

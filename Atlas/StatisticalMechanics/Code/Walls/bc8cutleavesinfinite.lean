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
import Code.Walls.bc4_core
import Code.Walls.bc4_nbrfinite
import Code.Walls.bc4_pigeonhole
import Code.Walls.bc3_distinctwitnessclusters

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}
























theorem bc8_cutLeavesInfinite (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hinf : (cluster d ω x).Infinite) (h0mem : (0 : Site d) ∈ cluster d ω x) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧ (cluster d (removeSite 0 ω) n).Infinite := by
  
  have hdiff : (cluster d ω x \ {(0 : Site d)}).Infinite :=
    hinf.diff (Set.finite_singleton _)
  
  have hNfin : {n : Site d | (openSubgraph d ω).Adj 0 n}.Finite :=
    bc4_origin_openNeighbours_finite ω
  
  have hUinf :
      (⋃ n ∈ {n : Site d | (openSubgraph d ω).Adj 0 n},
          cluster d (removeSite 0 ω) n).Infinite :=
    hdiff.mono (bc4c_punctured_cluster_subset_neighbour_cutClusters ω h0mem)
  
  obtain ⟨n, hnN, hninf⟩ := bc4_finite_biUnion_infinite hNfin hUinf
  exact ⟨n, hnN, hninf⟩











theorem bc8_cutLeavesInfinite_inCluster (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hinf : (cluster d ω x).Infinite) (h0mem : (0 : Site d) ∈ cluster d ω x) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧ n ∈ cluster d ω x ∧
      (cluster d (removeSite 0 ω) n).Infinite := by
  obtain ⟨n, hadj, hninf⟩ := bc8_cutLeavesInfinite ω hinf h0mem
  refine ⟨n, hadj, ?_, hninf⟩
  
  rw [mem_cluster]
  exact (mem_cluster.mp h0mem).trans hadj.reachable




theorem bc8_origin_openNeighbours_ncard_le (ω : ConfigSpace (Sym2 (Site d))) :
    {n : Site d | (openSubgraph d ω).Adj 0 n}.ncard ≤ 2 * d :=
  bc4_origin_openNeighbours_ncard_le ω













theorem bc8_originCutLeavesInfinite (ω : ConfigSpace (Sym2 (Site d))) :
    bc3_OriginCutLeavesInfinite ω := by
  intro x hinf h0mem
  obtain ⟨n, _hadj, hmem, hninf⟩ := bc8_cutLeavesInfinite_inCluster ω hinf h0mem
  exact ⟨n, hmem, hninf⟩











theorem bc8_cutLeavesInfinite_origin (ω : ConfigSpace (Sym2 (Site d)))
    (hinf : (cluster d ω 0).Infinite) :
    ∃ n, (openSubgraph d ω).Adj 0 n ∧ (cluster d (removeSite 0 ω) n).Infinite :=
  bc8_cutLeavesInfinite ω hinf (self_mem_cluster ω 0)

end Walls

end StatMech

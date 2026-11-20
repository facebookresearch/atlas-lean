/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























import Mathlib
import Code.Percolation.CorridorSidesFromClusters
import Code.Percolation.HrouteHighDim

namespace StatMech.Walls

open SimpleGraph
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open StatMech.Percolation.DisjointPaths

variable {d : ℕ}




theorem bkm_origin_no_neighbour (ω : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    ¬ (openSubgraph d (removeSite 0 ω)).Adj 0 w := by
  intro h
  rw [openSubgraph_adj] at h
  have hmem : (0 : Site d) ∈ s((0 : Site d), w) := Sym2.mem_mk_left 0 w
  rw [removeSite_apply_of_mem hmem] at h
  exact absurd h.2 (by simp)




theorem bkm_reachable_origin_eq (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (hy : Connected d (removeSite 0 ω) 0 y) : y = 0 := by
  obtain ⟨w⟩ := hy
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (bkm_origin_no_neighbour ω _)




theorem bkm_cluster_removeSite_origin_eq_singleton (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite 0 ω) 0 = {0} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨self_mem_cluster (removeSite 0 ω) 0, fun y hy => ?_⟩
  exact bkm_reachable_origin_eq ω (mem_cluster.mp hy)



theorem bkm_cluster_removeSite_origin_finite (ω : ConfigSpace (Sym2 (Site d))) :
    (cluster d (removeSite 0 ω) 0).Finite := by
  rw [bkm_cluster_removeSite_origin_eq_singleton]
  exact Set.finite_singleton 0


theorem bkm_cluster_removeSite_origin_not_infinite (ω : ConfigSpace (Sym2 (Site d))) :
    ¬ (cluster d (removeSite 0 ω) 0).Infinite :=
  Set.not_infinite.mpr (bkm_cluster_removeSite_origin_finite ω)






theorem bkm_witness_ne_zero (ω : ConfigSpace (Sym2 (Site d))) {w : Site d}
    (hinf : (cluster d (removeSite 0 ω) w).Infinite) : w ≠ 0 := by
  rintro rfl
  exact bkm_cluster_removeSite_origin_not_infinite ω hinf





theorem bkm_witnesses_ne_zero (ω : ConfigSpace (Sym2 (Site d)))
    (h : csc_DistinctClusterCorridors ω) :
    ∃ (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) (w₁ w₂ w₃ : Site d),
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃) ∧
      (Relation.ReflTransGen (CorridorStep G) a₁ w₁ ∧
        Relation.ReflTransGen (CorridorStep G) a₂ w₂ ∧
        Relation.ReflTransGen (CorridorStep G) a₃ w₃) ∧
      ((cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite) ∧
      (¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₁ a₂ ∧
        ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₁ a₃ ∧
        ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₂ a₃) ∧
      (w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0) := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, hcorr, hinf, hsep⟩ := h
  exact ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, hcorr, hinf, hsep,
    bkm_witness_ne_zero _ hinf.1, bkm_witness_ne_zero _ hinf.2.1,
    bkm_witness_ne_zero _ hinf.2.2⟩

end StatMech.Walls

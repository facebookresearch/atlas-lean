/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting

/-!
# The origin after removing it

Without the origin, its cluster is `{0}`, so a site with infinite cluster there is not the origin;
corridor witnesses differ from the origin.

## i. Overview

In `removeSite 0 ω` the origin has no open neighbour, so it is connected only to itself and its
cluster is `{0}`, which is finite. Hence a site whose cluster without the origin is infinite is not
the origin, and the witnesses of distinct-cluster corridors are nonzero.

## ii. Key results

- `bkm_cluster_removeSite_origin_eq_singleton` : the cluster of the origin is `{0}`.
- `bkm_witnesses_ne_zero` : corridor witnesses are nonzero.

## iii. Table of contents

- A. The cluster of the origin
- B. Witnesses

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

namespace StatMech.Walls

open SimpleGraph
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open StatMech.Percolation.DisjointPaths

variable {d : ℕ}

/-! ## A. The cluster of the origin -/

lemma bkm_origin_no_neighbour (ω : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    ¬ (openSubgraph d (removeSite 0 ω)).Adj 0 w := by
  intro h
  rw [openSubgraph_adj] at h
  have hmem : (0 : Site d) ∈ s((0 : Site d), w) := Sym2.mem_mk_left 0 w
  rw [removeSite_apply_of_mem hmem] at h
  exact absurd h.2 (by simp)

lemma bkm_reachable_origin_eq (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (hy : Connected d (removeSite 0 ω) 0 y) : y = 0 := by
  obtain ⟨w⟩ := hy
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (bkm_origin_no_neighbour ω _)

lemma bkm_cluster_removeSite_origin_eq_singleton (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite 0 ω) 0 = {0} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨self_mem_cluster (removeSite 0 ω) 0, fun y hy => ?_⟩
  exact bkm_reachable_origin_eq ω (mem_cluster.mp hy)

lemma bkm_cluster_removeSite_origin_finite (ω : ConfigSpace (Sym2 (Site d))) :
    (cluster d (removeSite 0 ω) 0).Finite := by
  rw [bkm_cluster_removeSite_origin_eq_singleton]
  exact Set.finite_singleton 0

lemma bkm_cluster_removeSite_origin_not_infinite (ω : ConfigSpace (Sym2 (Site d))) :
    ¬ (cluster d (removeSite 0 ω) 0).Infinite :=
  Set.not_infinite.mpr (bkm_cluster_removeSite_origin_finite ω)

/-! ## B. Witnesses -/

lemma bkm_witness_ne_zero (ω : ConfigSpace (Sym2 (Site d))) {w : Site d}
    (hinf : (cluster d (removeSite 0 ω) w).Infinite) : w ≠ 0 := by
  rintro rfl
  exact bkm_cluster_removeSite_origin_not_infinite ω hinf

lemma bkm_witnesses_ne_zero (ω : ConfigSpace (Sym2 (Site d)))
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

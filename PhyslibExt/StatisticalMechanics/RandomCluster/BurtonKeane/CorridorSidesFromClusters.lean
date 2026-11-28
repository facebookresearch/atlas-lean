/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting

/-!
# Corridor sides from distinct clusters

Clusters give disjoint closed sides, so corridors ending in three distinct clusters give disjoint
corridor routing and corridor covers.

## i. Overview

Clusters are closed under open edges and disconnected sites have disjoint clusters.
`csc_DistinctClusterCorridors ω` asks for three neighbours of the origin and a forced edge set
routing them by corridors to sites in three distinct clusters of the cut configuration. It gives
disjoint corridor routing, and for every configuration of `threeMeetBox d n` a corridor cover.

## ii. Key results

- `csc_disjointCorridorRouting_of_distinctClusters` : disjoint routing from distinct-cluster
  corridors.

## iii. Table of contents

- A. Distinct-cluster corridors

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

namespace StatMech.Percolation

open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation.DisjointPaths

variable {d : ℕ}

/-! ## A. Distinct-cluster corridors -/

lemma csc_cluster_adjClosed (ω' : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    ∀ u v, u ∈ cluster d ω' x → (openSubgraph d ω').Adj u v → v ∈ cluster d ω' x := by
  intro u v hu hadj
  rw [mem_cluster] at hu ⊢
  exact hu.trans hadj.reachable

lemma csc_clusters_disjoint (ω' : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (h : ¬ Connected d ω' x y) : Disjoint (cluster d ω' x) (cluster d ω' y) := by
  rw [Set.disjoint_left]
  intro w hwx hwy
  rw [mem_cluster] at hwx hwy
  exact h (hwx.trans hwy.symm)

/-- Three distinct neighbours of the origin and a forced edge set routing them along corridors to
sites
`w i` with infinite cut clusters lying in three distinct clusters of the cut configuration. -/
def csc_DistinctClusterCorridors (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
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
      ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₂ a₃)

lemma csc_disjointCorridorRouting_of_distinctClusters (ω : ConfigSpace (Sym2 (Site d)))
    (h : csc_DistinctClusterCorridors ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, hcorr, hinf, hsep⟩ := h
  set ω' : ConfigSpace (Sym2 (Site d)) := removeSite 0 (forceOpenFinset G ω) with hω'
  refine ⟨a₁, a₂, a₃, G, w₁, w₂, w₃,
    cluster d ω' a₁, cluster d ω' a₂, cluster d ω' a₃,
    hne, hadj, hcorr, hinf, ?_, ?_, ?_⟩
  · exact ⟨mem_cluster.mpr (connected_refl ω' a₁), mem_cluster.mpr (connected_refl ω' a₂),
      mem_cluster.mpr (connected_refl ω' a₃)⟩
  · exact ⟨csc_cluster_adjClosed ω' a₁, csc_cluster_adjClosed ω' a₂, csc_cluster_adjClosed ω' a₃⟩
  · exact ⟨csc_clusters_disjoint ω' hsep.1, csc_clusters_disjoint ω' hsep.2.1,
      csc_clusters_disjoint ω' hsep.2.2⟩

lemma csc_corridorCover_of_distinctClusters {n : ℕ}
    (h : ∀ ω ∈ threeMeetBox d n, csc_DistinctClusterCorridors ω) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G :=
  corridorCover_of_routing (fun ω hω => csc_disjointCorridorRouting_of_distinctClusters ω (h ω hω))

end StatMech.Percolation

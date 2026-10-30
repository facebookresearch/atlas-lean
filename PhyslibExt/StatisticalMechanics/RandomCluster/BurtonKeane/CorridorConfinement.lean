/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting

/-!
# Corridor confinement by distinct clusters

Distinct clusters are disjoint regions closed under open edges, so three distinct clusters confine
three corridors; this gives disjoint corridor routing.

## i. Overview

Clusters are closed under open edges and distinct clusters are disjoint, so three distinct clusters
give three disjoint confining sides; conversely disjoint closed sides force distinct clusters. Axis
corridors are chains of corridor steps. `bcc_distinct_clusters_residue ω` asks for three neighbours
of the origin and a forced edge set routing them to infinite clusters lying in three distinct
clusters of the cut configuration; it gives `DisjointCorridorRouting`.

## ii. Key results

- `bcc_disjoint_sides_iff_clusters_distinct` : disjoint sides are distinct clusters.
- `bcc_disjointRouting_of_residue` : disjoint routing from the residue.

## iii. Table of contents

- A. Clusters as sides
- B. The distinct-cluster residue

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}

/-! ## A. Clusters as sides -/

/-- Same statement as `csc_cluster_adjClosed`; kept because TrifurcationExistence uses it. -/
lemma bcc_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (a : Site d) :
    ∀ u v, u ∈ cluster d ϱ a → (openSubgraph d ϱ).Adj u v → v ∈ cluster d ϱ a := by
  intro u v hu hadj
  rw [mem_cluster] at hu ⊢
  exact hu.trans (SimpleGraph.Adj.reachable hadj)

lemma bcc_cluster_disjoint_of_ne (ϱ : ConfigSpace (Sym2 (Site d))) (a b : Site d)
    (hne : cluster d ϱ a ≠ cluster d ϱ b) : Disjoint (cluster d ϱ a) (cluster d ϱ b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  rw [mem_cluster] at hxa hxb
  exact hne (by rw [cluster_eq_of_connected hxa, cluster_eq_of_connected hxb])

lemma bcc_disjoint_confining_sides
    (ϱ : ConfigSpace (Sym2 (Site d))) (a₁ a₂ a₃ : Site d)
    (hd12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂)
    (hd13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃)
    (hd23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃) :
    ∃ S₁ S₂ S₃ : Set (Site d),
      (a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃) ∧
      ((∀ u v, u ∈ S₁ → (openSubgraph d ϱ).Adj u v → v ∈ S₁) ∧
        (∀ u v, u ∈ S₂ → (openSubgraph d ϱ).Adj u v → v ∈ S₂) ∧
        (∀ u v, u ∈ S₃ → (openSubgraph d ϱ).Adj u v → v ∈ S₃)) ∧
      (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃) :=
  ⟨cluster d ϱ a₁, cluster d ϱ a₂, cluster d ϱ a₃,
    ⟨self_mem_cluster ϱ a₁, self_mem_cluster ϱ a₂, self_mem_cluster ϱ a₃⟩,
    ⟨bcc_cluster_adjClosed ϱ a₁, bcc_cluster_adjClosed ϱ a₂, bcc_cluster_adjClosed ϱ a₃⟩,
    bcc_cluster_disjoint_of_ne ϱ a₁ a₂ hd12, bcc_cluster_disjoint_of_ne ϱ a₁ a₃ hd13,
    bcc_cluster_disjoint_of_ne ϱ a₂ a₃ hd23⟩

lemma bcc_corridorWorks_of_distinct_clusters (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d)))
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite)
    (hd12 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₂)
    (hd13 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃)
    (hd23 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₂
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃) :
    ω ∈ CorridorWorks a₁ a₂ a₃ G := by
  set ϱ := removeSite 0 (forceOpenFinset G ω) with hϱ
  exact corridorWorks_of_separated ω a₁ a₂ a₃ G hne hadj
    (cluster d ϱ a₁) (cluster d ϱ a₂) (cluster d ϱ a₃)
    (self_mem_cluster ϱ a₁) (self_mem_cluster ϱ a₂) (self_mem_cluster ϱ a₃)
    (bcc_cluster_adjClosed ϱ a₁) (bcc_cluster_adjClosed ϱ a₂) (bcc_cluster_adjClosed ϱ a₃)
    (bcc_cluster_disjoint_of_ne ϱ a₁ a₂ hd12) (bcc_cluster_disjoint_of_ne ϱ a₁ a₃ hd13)
    (bcc_cluster_disjoint_of_ne ϱ a₂ a₃ hd23) hinf

lemma bcc_disjoint_sides_iff_clusters_distinct
    (ϱ : ConfigSpace (Sym2 (Site d))) (a₁ a₂ a₃ : Site d) :
    (∃ S₁ S₂ S₃ : Set (Site d),
      (a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃) ∧
      ((∀ u v, u ∈ S₁ → (openSubgraph d ϱ).Adj u v → v ∈ S₁) ∧
        (∀ u v, u ∈ S₂ → (openSubgraph d ϱ).Adj u v → v ∈ S₂) ∧
        (∀ u v, u ∈ S₃ → (openSubgraph d ϱ).Adj u v → v ∈ S₃)) ∧
      (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃)) ↔
    (cluster d ϱ a₁ ≠ cluster d ϱ a₂ ∧ cluster d ϱ a₁ ≠ cluster d ϱ a₃ ∧
      cluster d ϱ a₂ ≠ cluster d ϱ a₃) := by
  constructor
  · rintro ⟨S₁, S₂, S₃, ⟨hm1, hm2, hm3⟩, ⟨hcl1, hcl2, hcl3⟩, hd12, hd13, hd23⟩
    have hs1 := StatMech.Percolation.DisjointPaths.cluster_subset_of_adjClosed ϱ S₁ a₁ hm1 hcl1
    have hs2 := StatMech.Percolation.DisjointPaths.cluster_subset_of_adjClosed ϱ S₂ a₂ hm2 hcl2
    have hs3 := StatMech.Percolation.DisjointPaths.cluster_subset_of_adjClosed ϱ S₃ a₃ hm3 hcl3
    exact ⟨cluster_ne_of_disjoint ϱ a₁ a₂ S₁ S₂ hs1 hs2 hd12,
      cluster_ne_of_disjoint ϱ a₁ a₃ S₁ S₃ hs1 hs3 hd13,
      cluster_ne_of_disjoint ϱ a₂ a₃ S₂ S₃ hs2 hs3 hd23⟩
  · rintro ⟨hd12, hd13, hd23⟩
    exact bcc_disjoint_confining_sides ϱ a₁ a₂ a₃ hd12 hd13 hd23

lemma bcc_axisCorridor_corridorStep (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges j L))
      (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) := by
  suffices H : ∀ m : ℕ, 1 ≤ m → m ≤ L →
      Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges j L))
        (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) by
    have := H L hL le_rfl; simpa using this
  intro m
  induction m with
  | zero => intro h; omega
  | succ p ih =>
    intro _ hpL
    rcases Nat.lt_or_ge 1 (p + 1) with hp | hp
    · have hp1 : 1 ≤ p := by omega
      have hppL : p < L := by omega
      have hrec := ih hp1 (by omega)
      have hstep : CorridorStep (hrHD_corridorEdges j L)
          (hrHD_rayPt j (p : ℤ)) (hrHD_rayPt j ((p : ℤ) + 1)) :=
        ⟨hrHD_adj_rayPt j (p : ℤ), hrHD_mem_corridorEdges hppL,
          hrHD_origin_notMem_rayEdge j (p : ℤ) (by exact_mod_cast hp1)⟩
      have hgoal := hrec.tail hstep
      have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [he] at hgoal
    · have hp1 : p + 1 = 1 := by omega
      rw [hp1]; simpa using Relation.ReflTransGen.refl

lemma bcc_disjointRouting_of_corridors_and_distinct (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) (w₁ w₂ w₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hcor₁ : Relation.ReflTransGen (CorridorStep G) a₁ w₁)
    (hcor₂ : Relation.ReflTransGen (CorridorStep G) a₂ w₂)
    (hcor₃ : Relation.ReflTransGen (CorridorStep G) a₃ w₃)
    (hw₁ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite)
    (hw₂ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite)
    (hw₃ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite)
    (hd12 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₂)
    (hd13 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃)
    (hd23 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₂
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃) :
    DisjointCorridorRouting ω := by
  set ϱ := removeSite 0 (forceOpenFinset G ω) with hϱ
  exact ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, cluster d ϱ a₁, cluster d ϱ a₂, cluster d ϱ a₃,
    hne, hadj, ⟨hcor₁, hcor₂, hcor₃⟩, ⟨hw₁, hw₂, hw₃⟩,
    ⟨self_mem_cluster ϱ a₁, self_mem_cluster ϱ a₂, self_mem_cluster ϱ a₃⟩,
    ⟨bcc_cluster_adjClosed ϱ a₁, bcc_cluster_adjClosed ϱ a₂, bcc_cluster_adjClosed ϱ a₃⟩,
    bcc_cluster_disjoint_of_ne ϱ a₁ a₂ hd12, bcc_cluster_disjoint_of_ne ϱ a₁ a₃ hd13,
    bcc_cluster_disjoint_of_ne ϱ a₂ a₃ hd23⟩

/-! ## B. The distinct-cluster residue -/

/-- Three distinct neighbours of the origin and a forced edge set avoiding the origin connecting
them to
sites `w i` with infinite cut clusters, in three distinct clusters of the cut configuration. -/
def bcc_distinct_clusters_residue (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
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
    (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₂ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) a₂
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃)

lemma bcc_disjointRouting_of_residue (ω : ConfigSpace (Sym2 (Site d)))
    (h : bcc_distinct_clusters_residue ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩,
    hd12, hd13, hd23⟩ := h
  exact bcc_disjointRouting_of_corridors_and_distinct ω a₁ a₂ a₃ G w₁ w₂ w₃
    hne hadj hc1 hc2 hc3 hw1 hw2 hw3 hd12 hd13 hd23

end Percolation

end StatMech

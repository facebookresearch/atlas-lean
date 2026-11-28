/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters

/-!
# Closed barriers block connections

A set closed under open edges cannot be left by an open path; two sites are disconnected exactly
when such a set separates them.

## i. Overview

`bc3_AdjClosed ϱ R` says every open edge from `R` stays in `R`. Then clusters of sites of `R` lie in
`R`, and no site of `R` is connected to a site outside it. Clusters and their complements are
closed, so two sites are disconnected iff some closed set contains one and not the other.

## ii. Key results

- `bc3_barrier_blocks` : a closed set blocks connections.
- `bc3_barrier_blocks_iff_cluster` : disconnection is separation by a closed set.

## iii. Table of contents

- A. Closed sets

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Closed sets -/

/-- Every open edge of `ϱ` from a site of `R` ends in `R`. -/
def bc3_AdjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (R : Set (Site d)) : Prop :=
  ∀ u v, u ∈ R → (openSubgraph d ϱ).Adj u v → v ∈ R

lemma bc3_cluster_subset_of_adjClosed (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (a : Site d) (ha : a ∈ R) (hcl : bc3_AdjClosed ϱ R) :
    cluster d ϱ a ⊆ R :=
  cluster_subset_of_adjClosed ϱ R a ha hcl

lemma bc3_barrier_blocks (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc3_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ p q := by
  intro hconn
  exact hq (bc3_cluster_subset_of_adjClosed ϱ R p hp hcl (by rwa [mem_cluster]))

lemma bc3_barrier_blocks_symm (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc3_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ q p :=
  fun h => bc3_barrier_blocks ϱ R p q hcl hp hq h.symm

lemma bc3_mem_of_connected (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc3_AdjClosed ϱ R) (hp : p ∈ R) (hconn : Connected d ϱ p q) :
    q ∈ R :=
  bc3_cluster_subset_of_adjClosed ϱ R p hp hcl (by rwa [mem_cluster])

lemma bc3_disconnected_of_barrier_split (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc3_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p :=
  ⟨bc3_barrier_blocks ϱ R p q hcl hp hq, bc3_barrier_blocks_symm ϱ R p q hcl hp hq⟩

lemma bc3_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    bc3_AdjClosed ϱ (cluster d ϱ w) :=
  fun u v hu hadj => Percolation.csc_cluster_adjClosed ϱ w u v hu hadj

lemma bc3_compl_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    bc3_AdjClosed ϱ (cluster d ϱ w)ᶜ := by
  intro u v hu hadj hv
  exact hu (Percolation.csc_cluster_adjClosed ϱ w _ _ hv hadj.symm)

lemma bc3_barrier_blocks_iff_cluster (ϱ : ConfigSpace (Sym2 (Site d))) (p q : Site d) :
    (¬ Connected d ϱ p q) ↔
      ∃ R : Set (Site d), bc3_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R := by
  constructor
  · intro hncon
    refine ⟨cluster d ϱ p, bc3_cluster_adjClosed ϱ p, self_mem_cluster ϱ p, ?_⟩
    rw [mem_cluster]; exact hncon
  · rintro ⟨R, hcl, hp, hq⟩
    exact bc3_barrier_blocks ϱ R p q hcl hp hq

lemma bc3_barrierblocks (ϱ : ConfigSpace (Sym2 (Site d))) :
    (∀ (R : Set (Site d)) (p q : Site d),
        bc3_AdjClosed ϱ R → p ∈ R → q ∉ R →
        ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p) ∧
      (∀ p q : Site d,
        (¬ Connected d ϱ p q) ↔
          ∃ R : Set (Site d), bc3_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R) :=
  ⟨fun R p q hcl hp hq => bc3_disconnected_of_barrier_split ϱ R p q hcl hp hq,
    fun p q => bc3_barrier_blocks_iff_cluster ϱ p q⟩

end Walls

end StatMech

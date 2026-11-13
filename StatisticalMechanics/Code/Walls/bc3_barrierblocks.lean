/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import Code.Percolation.HrouteDisjointPaths
import Code.Percolation.MengerRouting

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}







def bc3_AdjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (R : Set (Site d)) : Prop :=
  ∀ u v, u ∈ R → (openSubgraph d ϱ).Adj u v → v ∈ R











theorem bc3_cluster_subset_of_adjClosed (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (a : Site d) (ha : a ∈ R) (hcl : bc3_AdjClosed ϱ R) :
    cluster d ϱ a ⊆ R :=
  cluster_subset_of_adjClosed ϱ R a ha hcl









theorem bc3_barrier_blocks (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc3_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ p q := by
  intro hconn
  exact hq (bc3_cluster_subset_of_adjClosed ϱ R p hp hcl (by rwa [mem_cluster]))



theorem bc3_barrier_blocks_symm (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc3_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ q p :=
  fun h => bc3_barrier_blocks ϱ R p q hcl hp hq h.symm




theorem bc3_mem_of_connected (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc3_AdjClosed ϱ R) (hp : p ∈ R) (hconn : Connected d ϱ p q) :
    q ∈ R :=
  bc3_cluster_subset_of_adjClosed ϱ R p hp hcl (by rwa [mem_cluster])








theorem bc3_disconnected_of_barrier_split (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc3_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p :=
  ⟨bc3_barrier_blocks ϱ R p q hcl hp hq, bc3_barrier_blocks_symm ϱ R p q hcl hp hq⟩






theorem bc3_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    bc3_AdjClosed ϱ (cluster d ϱ w) :=
  fun _ _ hu hadj => mng_cluster_adjClosed ϱ w hu hadj






theorem bc3_compl_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    bc3_AdjClosed ϱ (cluster d ϱ w)ᶜ := by
  intro u v hu hadj hv
  
  exact hu (mng_cluster_adjClosed ϱ w hv hadj.symm)











theorem bc3_barrier_blocks_iff_cluster (ϱ : ConfigSpace (Sym2 (Site d))) (p q : Site d) :
    (¬ Connected d ϱ p q) ↔
      ∃ R : Set (Site d), bc3_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R := by
  constructor
  · intro hncon
    refine ⟨cluster d ϱ p, bc3_cluster_adjClosed ϱ p, self_mem_cluster ϱ p, ?_⟩
    rw [mem_cluster]; exact hncon
  · rintro ⟨R, hcl, hp, hq⟩
    exact bc3_barrier_blocks ϱ R p q hcl hp hq


















theorem bc3_barrierblocks (ϱ : ConfigSpace (Sym2 (Site d))) :
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































































import Mathlib
import Code.Percolation.HrouteDisjointPaths
import Code.Percolation.MengerRouting
import Code.Walls.bc2_core

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}







def bc5_AdjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (R : Set (Site d)) : Prop :=
  ∀ u v, u ∈ R → (openSubgraph d ϱ).Adj u v → v ∈ R











theorem bc5_cluster_subset_of_adjClosed (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (a : Site d) (ha : a ∈ R) (hcl : bc5_AdjClosed ϱ R) :
    cluster d ϱ a ⊆ R :=
  cluster_subset_of_adjClosed ϱ R a ha hcl






theorem bc5_mem_of_connected (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc5_AdjClosed ϱ R) (hp : p ∈ R) (hconn : Connected d ϱ p q) :
    q ∈ R :=
  bc5_cluster_subset_of_adjClosed ϱ R p hp hcl (by rwa [mem_cluster])







theorem bc5_barrier_blocks (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc5_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ p q :=
  fun hconn => hq (bc5_mem_of_connected ϱ R p q hcl hp hconn)



theorem bc5_barrier_blocks_symm (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc5_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ q p :=
  fun h => bc5_barrier_blocks ϱ R p q hcl hp hq h.symm








theorem bc5_disconnected_of_barrier_split (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc5_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p :=
  ⟨bc5_barrier_blocks ϱ R p q hcl hp hq, bc5_barrier_blocks_symm ϱ R p q hcl hp hq⟩






theorem bc5_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    bc5_AdjClosed ϱ (cluster d ϱ w) :=
  fun _ _ hu hadj => mng_cluster_adjClosed ϱ w hu hadj






theorem bc5_compl_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    bc5_AdjClosed ϱ (cluster d ϱ w)ᶜ := by
  intro u v hu hadj hv
  exact hu (mng_cluster_adjClosed ϱ w hv hadj.symm)











theorem bc5_barrier_blocks_iff_cluster (ϱ : ConfigSpace (Sym2 (Site d))) (p q : Site d) :
    (¬ Connected d ϱ p q) ↔
      ∃ R : Set (Site d), bc5_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R := by
  constructor
  · intro hncon
    refine ⟨cluster d ϱ p, bc5_cluster_adjClosed ϱ p, self_mem_cluster ϱ p, ?_⟩
    rw [mem_cluster]; exact hncon
  · rintro ⟨R, hcl, hp, hq⟩
    exact bc5_barrier_blocks ϱ R p q hcl hp hq














noncomputable abbrev bc5_corridorCut (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) : ConfigSpace (Sym2 (Site d)) :=
  removeSite 0 (forceOpenFinset
    (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
      hrHD_corridorEdges j₃ (L₃ + 1)) ω)






theorem bc5_pairwiseSeparated_of_barriers (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (R₁₂ R₁₃ R₂₃ : Set (Site d))
    (hcl12 : bc5_AdjClosed (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) R₁₂)
    (h12p : hrHD_rayPt j₁ 1 ∈ R₁₂) (h12q : hrHD_rayPt j₂ 1 ∉ R₁₂)
    (hcl13 : bc5_AdjClosed (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) R₁₃)
    (h13p : hrHD_rayPt j₁ 1 ∈ R₁₃) (h13q : hrHD_rayPt j₃ 1 ∉ R₁₃)
    (hcl23 : bc5_AdjClosed (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) R₂₃)
    (h23p : hrHD_rayPt j₂ 1 ∈ R₂₃) (h23q : hrHD_rayPt j₃ 1 ∉ R₂₃) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ :=
  ⟨bc5_barrier_blocks _ R₁₂ _ _ hcl12 h12p h12q,
   bc5_barrier_blocks _ R₁₃ _ _ hcl13 h13p h13q,
   bc5_barrier_blocks _ R₂₃ _ _ hcl23 h23p h23q⟩









theorem bc5_pairwiseSeparated_of_clusterBarriers (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (h12 : ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃)
      (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
    (h13 : ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃)
      (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
    (h23 : ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃)
      (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ :=
  bc5_pairwiseSeparated_of_barriers ω j₁ j₂ j₃ L₁ L₂ L₃
    (cluster d _ (hrHD_rayPt j₁ 1)) (cluster d _ (hrHD_rayPt j₁ 1))
    (cluster d _ (hrHD_rayPt j₂ 1))
    (bc5_cluster_adjClosed _ _) (self_mem_cluster _ _) (by rw [mem_cluster]; exact h12)
    (bc5_cluster_adjClosed _ _) (self_mem_cluster _ _) (by rw [mem_cluster]; exact h13)
    (bc5_cluster_adjClosed _ _) (self_mem_cluster _ _) (by rw [mem_cluster]; exact h23)








theorem bc5_pairwiseSeparated_iff_cutDisconnected (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ ↔
      (¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃)
          (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) ∧
        ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃)
          (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) ∧
        ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃)
          (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :=
  ⟨fun h => h, fun ⟨h12, h13, h23⟩ =>
    bc5_pairwiseSeparated_of_clusterBarriers ω j₁ j₂ j₃ L₁ L₂ L₃ h12 h13 h23⟩



















theorem bc5_barrierblocks (ϱ : ConfigSpace (Sym2 (Site d))) :
    (∀ (R : Set (Site d)) (p q : Site d),
        bc5_AdjClosed ϱ R → p ∈ R → q ∉ R →
        ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p) ∧
      (∀ p q : Site d,
        (¬ Connected d ϱ p q) ↔
          ∃ R : Set (Site d), bc5_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R) :=
  ⟨fun R p q hcl hp hq => bc5_disconnected_of_barrier_split ϱ R p q hcl hp hq,
    fun p q => bc5_barrier_blocks_iff_cluster ϱ p q⟩

end Walls

end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMergeFreeMenger
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses

/-!
# Cluster attachment

Each of three distinct infinite clusters attaching to a neighbour of the origin through edges inside
it gives Menger attachment, merge-free insertion and disjoint routing.

## i. Overview

Edges inside a region keep walks in the region, so forced edges inside disjoint regions do not join
them, and forcing a subset is monotone. `bma_ClusterAttachment ω x` asks for a neighbour `a` of the
origin and a finite set of edges avoiding the origin, inside the cluster of `x`, whose forcing
connects `a` to `x` with infinite cut cluster. Three distinct clusters with attachments give Menger
attachment; the box version `bma_BoxClusterAttachment` gives merge-free insertion and disjoint
routing. Neighbours with infinite clusters satisfy it.

## ii. Key results

- `bma_attachment_of_three_clusterAttachments` : attachment data from three cluster attachments.
- `bma_disjointRouting_of_clusterAttachment` : disjoint routing from the box version.

## iii. Table of contents

- A. Edges inside regions
- B. Cluster attachment
- C. The box version

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

variable {d : ℕ}

/-! ## A. Edges inside regions -/

lemma bma_internal_of_edgesIn {R : Set (Site d)} {W : Finset (Sym2 (Site d))}
    (hW : ∀ e ∈ W, ∀ p, p ∈ e → p ∈ R) :
    ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R := by
  intro u v _ hmem
  exact hW _ hmem v (Sym2.mem_mk_right u v)

lemma bma_internal_of_edgesIn_disjoint {R S : Set (Site d)} {W : Finset (Sym2 (Site d))}
    (hW : ∀ e ∈ W, ∀ p, p ∈ e → p ∈ S) (hdisj : Disjoint R S) :
    ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R := by
  intro u v hu hmem
  have huS : u ∈ S := hW _ hmem u (Sym2.mem_mk_left u v)
  exact absurd (Set.disjoint_left.mp hdisj hu huS).elim (fun h => h)

lemma bma_internal_union {R₁ R₂ R₃ : Set (Site d)} {W₁ W₂ W₃ : Finset (Sym2 (Site d))}
    (h1 : ∀ e ∈ W₁, ∀ p, p ∈ e → p ∈ R₁) (h2 : ∀ e ∈ W₂, ∀ p, p ∈ e → p ∈ R₂)
    (h3 : ∀ e ∈ W₃, ∀ p, p ∈ e → p ∈ R₃)
    (hd12 : Disjoint R₁ R₂) (hd13 : Disjoint R₁ R₃) :
    ∀ u v, u ∈ R₁ → s(u, v) ∈ W₁ ∪ W₂ ∪ W₃ → v ∈ R₁ := by
  classical
  intro u v hu hmem
  rw [Finset.mem_union, Finset.mem_union] at hmem
  rcases hmem with (h | h) | h
  · exact bma_internal_of_edgesIn h1 u v hu h
  · exact bma_internal_of_edgesIn_disjoint h2 hd12 u v hu h
  · exact bma_internal_of_edgesIn_disjoint h3 hd13 u v hu h

lemma bma_originAvoiding_union {W₁ W₂ W₃ : Finset (Sym2 (Site d))}
    (h1 : ∀ e ∈ W₁, (0 : Site d) ∉ e) (h2 : ∀ e ∈ W₂, (0 : Site d) ∉ e)
    (h3 : ∀ e ∈ W₃, (0 : Site d) ∉ e) :
    ∀ e ∈ W₁ ∪ W₂ ∪ W₃, (0 : Site d) ∉ e := by
  classical
  intro e he
  rw [Finset.mem_union, Finset.mem_union] at he
  rcases he with (h | h) | h
  · exact h1 e h
  · exact h2 e h
  · exact h3 e h

lemma bma_removeSite_forceOpen_mono_sub (ω : ConfigSpace (Sym2 (Site d)))
    {Wⱼ W : Finset (Sym2 (Site d))} (hsub : Wⱼ ⊆ W) :
    removeSite 0 (forceOpenFinset Wⱼ ω) ≤ removeSite 0 (forceOpenFinset W ω) := by
  classical
  intro e
  by_cases h0 : (0 : Site d) ∈ e
  · simp [removeSite, h0]
  · simp only [removeSite, h0, ite_false]
    unfold forceOpenFinset
    by_cases hj : e ∈ Wⱼ
    · simp [hj, hsub hj]
    · by_cases hW : e ∈ W <;> simp [hj, hW]

lemma bma_connected_of_sub (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    {Wⱼ W : Finset (Sym2 (Site d))} (hsub : Wⱼ ⊆ W)
    (hc : Connected d (removeSite 0 (forceOpenFinset Wⱼ ω)) a x) :
    Connected d (removeSite 0 (forceOpenFinset W ω)) a x :=
  connected_mono (bma_removeSite_forceOpen_mono_sub ω hsub) hc

/-! ## B. Cluster attachment -/

/-- Some neighbour `a` of the origin and some finite set of edges avoiding the origin and lying in
the
cluster of `x`, such that after forcing them `a` is connected to `x` without the origin, with
infinite cluster. -/
def bma_ClusterAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ (a : Site d) (W : Finset (Sym2 (Site d))),
    (hypercubicLattice d).Adj 0 a ∧
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    (∀ e ∈ W, ∀ p, p ∈ e → p ∈ cluster d ω x) ∧
    a ∈ cluster d ω x ∧
    Connected d (removeSite 0 (forceOpenFinset W ω)) a x ∧
    (cluster d (removeSite 0 ω) x).Infinite

lemma bma_attachment_of_three_clusterAttachments (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : bma_ClusterAttachment ω x₁) (h2 : bma_ClusterAttachment ω x₂)
    (h3 : bma_ClusterAttachment ω x₃) :
    ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))),
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃) ∧
      (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      (a₁ ∈ cluster d ω x₁ ∧ a₂ ∈ cluster d ω x₂ ∧ a₃ ∈ cluster d ω x₃) ∧
      ((∀ u v, u ∈ cluster d ω x₁ → s(u, v) ∈ W → v ∈ cluster d ω x₁) ∧
        (∀ u v, u ∈ cluster d ω x₂ → s(u, v) ∈ W → v ∈ cluster d ω x₂) ∧
        (∀ u v, u ∈ cluster d ω x₃ → s(u, v) ∈ W → v ∈ cluster d ω x₃)) ∧
      (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧
        Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧
        Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧
      ((cluster d (removeSite 0 ω) x₁).Infinite ∧
        (cluster d (removeSite 0 ω) x₂).Infinite ∧
        (cluster d (removeSite 0 ω) x₃).Infinite) := by
  classical
  obtain ⟨a₁, W₁, hadj1, hW1, hin1, hmem1, hc1, hri1⟩ := h1
  obtain ⟨a₂, W₂, hadj2, hW2, hin2, hmem2, hc2, hri2⟩ := h2
  obtain ⟨a₃, W₃, hadj3, hW3, hin3, hmem3, hc3, hri3⟩ := h3
  have hd12 : Disjoint (cluster d ω x₁) (cluster d ω x₂) := Walls.bc2_disjoint_of_ne hcd12
  have hd13 : Disjoint (cluster d ω x₁) (cluster d ω x₃) := Walls.bc2_disjoint_of_ne hcd13
  have hd23 : Disjoint (cluster d ω x₂) (cluster d ω x₃) := Walls.bc2_disjoint_of_ne hcd23
  set W : Finset (Sym2 (Site d)) := W₁ ∪ W₂ ∪ W₃ with hWdef
  have hs1 : W₁ ⊆ W := by rw [hWdef]; exact (Finset.subset_union_left).trans
                            Finset.subset_union_left
  have hs2 : W₂ ⊆ W := by rw [hWdef]; exact (Finset.subset_union_right).trans
                            Finset.subset_union_left
  have hs3 : W₃ ⊆ W := by rw [hWdef]; exact Finset.subset_union_right
  refine ⟨a₁, a₂, a₃, W, ⟨hadj1, hadj2, hadj3⟩, ?_, ⟨hmem1, hmem2, hmem3⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨hri1, hri2, hri3⟩⟩
  · rw [hWdef]; exact bma_originAvoiding_union hW1 hW2 hW3
  · rw [hWdef]; exact bma_internal_union hin1 hin2 hin3 hd12 hd13
  · rw [hWdef]
    intro u v hu hmem
    rw [Finset.mem_union, Finset.mem_union] at hmem
    rcases hmem with (h | h) | h
    · exact bma_internal_of_edgesIn_disjoint hin1 hd12.symm u v hu h
    · exact bma_internal_of_edgesIn hin2 u v hu h
    · exact bma_internal_of_edgesIn_disjoint hin3 hd23 u v hu h
  · rw [hWdef]
    intro u v hu hmem
    rw [Finset.mem_union, Finset.mem_union] at hmem
    rcases hmem with (h | h) | h
    · exact bma_internal_of_edgesIn_disjoint hin1 hd13.symm u v hu h
    · exact bma_internal_of_edgesIn_disjoint hin2 hd23.symm u v hu h
    · exact bma_internal_of_edgesIn hin3 u v hu h
  · exact bma_connected_of_sub ω hs1 hc1
  · exact bma_connected_of_sub ω hs2 hc2
  · exact bma_connected_of_sub ω hs3 hc3

/-! ## C. The box version -/

/-- Box version: in every configuration of `threeMeetBox d n`, the sites of three distinct infinite
clusters meeting the box have cluster attachments. -/
def bma_BoxClusterAttachment (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      bma_ClusterAttachment ω x₁ ∧ bma_ClusterAttachment ω x₂ ∧ bma_ClusterAttachment ω x₃

lemma bma_boxMengerAttachment {n : ℕ}
    (h : bma_BoxClusterAttachment d n) : bmm_BoxMengerAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨ha1, ha2, ha3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact bma_attachment_of_three_clusterAttachments ω x₁ x₂ x₃ hcd12 hcd13 hcd23 ha1 ha2 ha3

lemma bma_boxMergeFreeInsertion_of_clusterAttachment {n : ℕ}
    (h : bma_BoxClusterAttachment d n) : tre_BoxMergeFreeInsertion d n :=
  bmm_boxMergeFreeInsertion_of_attachment (bma_boxMengerAttachment h)

lemma bma_disjointRouting_of_clusterAttachment {n : ℕ}
    (h : bma_BoxClusterAttachment d n) : hrHD_DisjointRouting d n :=
  bmm_disjointRouting_of_attachment (bma_boxMengerAttachment h)

lemma bma_clusterAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x := by
  classical
  refine ⟨x, ∅, hadj, ?_, ?_, self_mem_cluster ω x, ?_, hri⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · exact connected_rfl

lemma bma_three_clusterAttachments_of_neighbours (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    bma_ClusterAttachment ω x₁ ∧ bma_ClusterAttachment ω x₂ ∧ bma_ClusterAttachment ω x₃ :=
  ⟨bma_clusterAttachment_of_neighbour ω x₁ hadj.1 hri.1,
    bma_clusterAttachment_of_neighbour ω x₂ hadj.2.1 hri.2.1,
    bma_clusterAttachment_of_neighbour ω x₃ hadj.2.2 hri.2.2⟩

end Percolation

end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachment

/-!
# Attachment avoiding the origin

An infinite cluster of the configuration without the origin that contains a neighbour of the origin
gives an attachment by a walk avoiding the origin; this gives disjoint routing.

## i. Overview

Walks in a cluster stay in it, so a walk to a cluster not containing the origin avoids the origin.
In `removeSite 0 ω` the origin is isolated, so connections there give walks in `ω` avoiding the
origin. The residue `ava_AvoidingRoutingResidue ω x` asks that `x ≠ 0` have an infinite cluster
without the origin containing a neighbour of the origin. It gives avoiding attachment and cluster
attachment, and its box version `ava_BoxAvoidingRoutingResidue` gives disjoint routing. Neighbours
of the origin satisfy it.

## ii. Key results

- `ava_avoidingAttachment` : avoiding attachment from the residue.
- `ava_disjointRouting_of_boxResidue` : disjoint routing from the box residue.

## iii. Table of contents

- A. Walks avoiding the origin
- B. The avoiding residue
- C. The box residue

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

/-! ## A. Walks avoiding the origin -/

lemma ava_support_mem_cluster (ω : ConfigSpace (Sym2 (Site d))) {a x z : Site d}
    (w : (openSubgraph d ω).Walk a x) (hz : z ∈ w.support) :
    z ∈ cluster d ω x := by
  have hza : Connected d ω a z := (w.takeUntil z hz).reachable
  rw [mem_cluster]
  exact (Connected.symm w.reachable).trans hza

lemma ava_origin_notMem_support_of_notMem_cluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (w : (openSubgraph d ω).Walk a x)
    (h0 : (0 : Site d) ∉ cluster d ω x) :
    (0 : Site d) ∉ w.support :=
  fun hmem => h0 (ava_support_mem_cluster ω w hmem)

lemma ava_removeSite_openSubgraph_le (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (removeSite 0 ω) ≤ openSubgraph d ω := by
  intro x y h
  obtain ⟨hadj, hval⟩ := h
  refine ⟨hadj, ?_⟩
  by_cases h0 : (0 : Site d) ∈ s(x, y)
  · rw [removeSite_apply_of_mem h0] at hval; exact absurd hval (by simp)
  · rwa [removeSite_apply_of_notMem h0] at hval

/-- Same statement as `bkm_origin_no_neighbour`; kept because `CorridorWitnessRemoveSite` is not
imported by all its users. -/
lemma ava_origin_no_adj_removeSite (ω : ConfigSpace (Sym2 (Site d))) (y : Site d) :
    ¬ (openSubgraph d (removeSite 0 ω)).Adj (0 : Site d) y := by
  rintro ⟨hadj, hval⟩
  have h0 : (0 : Site d) ∈ s((0 : Site d), y) := Sym2.mem_mk_left _ _
  rw [removeSite_apply_of_mem h0] at hval
  exact absurd hval (by simp)

/-- Same statement as `bkm_reachable_origin_eq`; kept because `CorridorWitnessRemoveSite` is not
imported by all its users. -/
lemma ava_connected_origin_eq (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (h : Connected d (removeSite 0 ω) (0 : Site d) x) : x = 0 := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj p => exact absurd hadj (ava_origin_no_adj_removeSite ω _)

lemma ava_origin_notMem_cluster_removeSite (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hx : x ≠ 0) : (0 : Site d) ∉ cluster d (removeSite 0 ω) x := by
  rw [mem_cluster]
  intro h
  exact hx (ava_connected_origin_eq ω h.symm)

lemma ava_avoiding_walk_of_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hx : x ≠ 0) (hc : Connected d (removeSite 0 ω) a x) :
    ∃ w : (openSubgraph d ω).Walk a x, (0 : Site d) ∉ w.support := by
  obtain ⟨wr⟩ := hc
  refine ⟨wr.mapLe (ava_removeSite_openSubgraph_le ω), ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro hmem
  exact ava_origin_notMem_cluster_removeSite ω hx
    (ava_support_mem_cluster (removeSite 0 ω) wr hmem)

lemma ava_connected_of_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hc : Connected d (removeSite 0 ω) a x) : Connected d ω a x :=
  hc.mono (ava_removeSite_openSubgraph_le ω)

/-! ## B. The avoiding residue -/

/-- `x ≠ 0`, the cluster of `x` without the origin is infinite, and it contains a neighbour of the
origin. -/
def ava_AvoidingRoutingResidue (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  x ≠ 0 ∧ (cluster d (removeSite 0 ω) x).Infinite ∧
    ∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d (removeSite 0 ω) x

lemma ava_avoidingAttachment_of_removeSiteCluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (hx : x ≠ 0) (hadj : (hypercubicLattice d).Adj 0 a)
    (hmemR : a ∈ cluster d (removeSite 0 ω) x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  have hc : Connected d (removeSite 0 ω) a x := (mem_cluster.mp hmemR).symm
  have hmem : a ∈ cluster d ω x := by
    rw [mem_cluster]; exact ava_connected_of_removeSite ω (mem_cluster.mp hmemR)
  obtain ⟨w, hw⟩ := ava_avoiding_walk_of_removeSite ω hx hc
  exact ⟨a, w, hadj, hmem, hw, hri⟩

lemma ava_avoidingAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : ava_AvoidingRoutingResidue ω x) : cla_AvoidingAttachment ω x := by
  obtain ⟨hx, hri, a, hadj, hmemR⟩ := h
  exact ava_avoidingAttachment_of_removeSiteCluster ω hx hadj hmemR hri

lemma ava_clusterAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : ava_AvoidingRoutingResidue ω x) : bma_ClusterAttachment ω x :=
  cla_clusterAttachment_of_avoidingAttachment ω x (ava_avoidingAttachment ω x h)

lemma ava_avoidingAttachment_of_notMemCluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (hadj : (hypercubicLattice d).Adj 0 a) (hmem : a ∈ cluster d ω x)
    (h0 : (0 : Site d) ∉ cluster d ω x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  obtain ⟨w⟩ := (mem_cluster.mp hmem).symm
  exact ⟨a, w, hadj, hmem, ava_origin_notMem_support_of_notMem_cluster ω w h0, hri⟩

lemma ava_avoidingRoutingResidue_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    ava_AvoidingRoutingResidue ω x :=
  ⟨hadj.ne.symm, hri, x, hadj, self_mem_cluster (removeSite 0 ω) x⟩

/-! ## C. The box residue -/

/-- Box version: in every configuration of `threeMeetBox d n`, the sites of three distinct infinite
clusters meeting the box satisfy the avoiding residue. -/
def ava_BoxAvoidingRoutingResidue (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
        ava_AvoidingRoutingResidue ω x₃

lemma ava_boxAvoidingAttachment_of_boxResidue {n : ℕ}
    (h : ava_BoxAvoidingRoutingResidue d n) : cla_BoxAvoidingAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨h1, h2, h3⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨ava_avoidingAttachment ω x₁ h1, ava_avoidingAttachment ω x₂ h2,
    ava_avoidingAttachment ω x₃ h3⟩

lemma ava_disjointRouting_of_boxResidue {n : ℕ}
    (h : ava_BoxAvoidingRoutingResidue d n) : hrHD_DisjointRouting d n :=
  cla_disjointRouting_of_boxAvoiding (ava_boxAvoidingAttachment_of_boxResidue h)

lemma ava_three_residues_of_neighbours (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
      ava_AvoidingRoutingResidue ω x₃ :=
  ⟨ava_avoidingRoutingResidue_of_neighbour ω x₁ hadj.1 hri.1,
    ava_avoidingRoutingResidue_of_neighbour ω x₂ hadj.2.1 hri.2.1,
    ava_avoidingRoutingResidue_of_neighbour ω x₃ hadj.2.2 hri.2.2⟩

end Percolation

end StatMech

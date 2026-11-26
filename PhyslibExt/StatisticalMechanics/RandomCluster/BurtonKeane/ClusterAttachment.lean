/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerAttachment
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneAttachment
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutAvoidingSurvives
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRouting

/-!
# Attachment by walks avoiding the origin

An open walk avoiding the origin from a neighbour of the origin to a site survives removing the
origin and forcing edges, which gives cluster attachment, Menger attachment and disjoint routing.

## i. Overview

An open walk whose support avoids the origin survives `removeSite 0`, also after forcing edges.
`cla_AvoidingAttachment ω x` asks for a neighbour `a` of the origin in the cluster of `x` with such
a walk to `x`, and an infinite cluster without the origin. It gives cluster attachment, and its box
version `cla_BoxAvoidingAttachment` gives Menger attachment and disjoint routing. Neighbours with
infinite clusters satisfy it.

## ii. Key results

- `cla_clusterAttachment_of_avoidingAttachment` : cluster attachment from avoiding attachment.
- `cla_disjointRouting_of_boxAvoiding` : disjoint routing from the box version.

## iii. Table of contents

- A. Surviving walks
- B. Avoiding attachment
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

/-! ## A. Surviving walks -/

lemma cla_walk_survival_force (ω : ConfigSpace (Sym2 (Site d))) (W : Finset (Sym2 (Site d)))
    {a x : Site d} (w : (openSubgraph d ω).Walk a x) (hw : (0 : Site d) ∉ w.support) :
    Connected d (removeSite 0 (forceOpenFinset W ω)) a x := by
  induction w with
  | nil => exact connected_rfl
  | @cons u v t hadj p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    push Not at hw
    obtain ⟨h0u, h0rest⟩ := hw
    have hopen : IsOpenEdge d ω u v := hadj
    have h0v : (0 : Site d) ≠ v := fun h => h0rest (h ▸ p.start_mem_support)
    have h0e : (0 : Site d) ∉ s(u, v) := by
      simp only [Sym2.mem_iff]; push Not; exact ⟨fun h => h0u h, fun h => h0v h⟩
    have hsurv : IsOpenEdge d (removeSite 0 (forceOpenFinset W ω)) u v :=
      bka_isOpenEdge_survives ω W hopen h0e
    exact hsurv.connected.trans (ih h0rest)

lemma cla_clusterAttachment_of_avoidingWalk (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a) (hmem : a ∈ cluster d ω x)
    (w : (openSubgraph d ω).Walk a x) (hw : (0 : Site d) ∉ w.support)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x := by
  classical
  refine ⟨a, ∅, hadj, ?_, ?_, hmem, ?_, hri⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · exact cla_walk_survival_force ω ∅ w hw

/-! ## B. Avoiding attachment -/

/-- Some neighbour `a` of the origin in the cluster of `x` has an open walk to `x` avoiding the
origin,
and the cluster of `x` without the origin is infinite. -/
def cla_AvoidingAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ (a : Site d) (w : (openSubgraph d ω).Walk a x),
    (hypercubicLattice d).Adj 0 a ∧
    a ∈ cluster d ω x ∧
    (0 : Site d) ∉ w.support ∧
    (cluster d (removeSite 0 ω) x).Infinite

lemma cla_clusterAttachment_of_avoidingAttachment (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (h : cla_AvoidingAttachment ω x) : bma_ClusterAttachment ω x := by
  obtain ⟨a, w, hadj, hmem, hw, hri⟩ := h
  exact cla_clusterAttachment_of_avoidingWalk ω hadj hmem w hw hri

lemma cla_avoidingAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  refine ⟨x, SimpleGraph.Walk.nil, hadj, self_mem_cluster ω x, ?_, hri⟩
  simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
  exact hadj.ne

/-! ## C. The box version -/

/-- Box version: in every configuration of `threeMeetBox d n`, the sites of three distinct infinite
clusters meeting the box have avoiding attachments. -/
def cla_BoxAvoidingAttachment (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      cla_AvoidingAttachment ω x₁ ∧ cla_AvoidingAttachment ω x₂ ∧ cla_AvoidingAttachment ω x₃

lemma cla_boxClusterAttachment_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : bma_BoxClusterAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨ha1, ha2, ha3⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨cla_clusterAttachment_of_avoidingAttachment ω x₁ ha1,
    cla_clusterAttachment_of_avoidingAttachment ω x₂ ha2,
    cla_clusterAttachment_of_avoidingAttachment ω x₃ ha3⟩

lemma cla_boxMengerAttachment_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : bmm_BoxMengerAttachment d n :=
  bma_boxMengerAttachment (cla_boxClusterAttachment_of_boxAvoiding h)

lemma cla_disjointRouting_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : hrHD_DisjointRouting d n :=
  bma_disjointRouting_of_clusterAttachment (cla_boxClusterAttachment_of_boxAvoiding h)

lemma cla_three_avoidingAttachments_of_neighbours (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    cla_AvoidingAttachment ω x₁ ∧ cla_AvoidingAttachment ω x₂ ∧ cla_AvoidingAttachment ω x₃ :=
  ⟨cla_avoidingAttachment_of_neighbour ω x₁ hadj.1 hri.1,
    cla_avoidingAttachment_of_neighbour ω x₂ hadj.2.1 hri.2.1,
    cla_avoidingAttachment_of_neighbour ω x₃ hadj.2.2 hri.2.2⟩

end Percolation

end StatMech

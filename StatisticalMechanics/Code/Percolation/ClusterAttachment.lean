/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Percolation.BoxMengerAttachment
import Code.Percolation.BurtonKeaneAttachment

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}
















theorem cla_walk_survival_force (ω : ConfigSpace (Sym2 (Site d))) (W : Finset (Sym2 (Site d)))
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




theorem cla_walk_survival (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (w : (openSubgraph d ω).Walk a x) (hw : (0 : Site d) ∉ w.support) :
    Connected d (removeSite 0 ω) a x := by
  have h := cla_walk_survival_force ω ∅ w hw
  rwa [bka_forceOpenFinset_empty] at h















theorem cla_clusterAttachment_of_avoidingWalk (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a) (hmem : a ∈ cluster d ω x)
    (w : (openSubgraph d ω).Walk a x) (hw : (0 : Site d) ∉ w.support)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x := by
  classical
  refine ⟨a, ∅, hadj, ?_, ?_, hmem, ?_, hri⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · exact cla_walk_survival_force ω ∅ w hw

















def cla_AvoidingAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ (a : Site d) (w : (openSubgraph d ω).Walk a x),
    (hypercubicLattice d).Adj 0 a ∧
    a ∈ cluster d ω x ∧
    (0 : Site d) ∉ w.support ∧
    (cluster d (removeSite 0 ω) x).Infinite




theorem cla_clusterAttachment_of_avoidingAttachment (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (h : cla_AvoidingAttachment ω x) : bma_ClusterAttachment ω x := by
  obtain ⟨a, w, hadj, hmem, hw, hri⟩ := h
  exact cla_clusterAttachment_of_avoidingWalk ω hadj hmem w hw hri












theorem cla_avoidingAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  refine ⟨x, SimpleGraph.Walk.nil, hadj, self_mem_cluster ω x, ?_, hri⟩
  simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
  exact hadj.ne




theorem cla_clusterAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x :=
  cla_clusterAttachment_of_avoidingAttachment ω x
    (cla_avoidingAttachment_of_neighbour ω x hadj hri)














def cla_BoxAvoidingAttachment (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      cla_AvoidingAttachment ω x₁ ∧ cla_AvoidingAttachment ω x₂ ∧ cla_AvoidingAttachment ω x₃




theorem cla_boxClusterAttachment_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : bma_BoxClusterAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨ha1, ha2, ha3⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨cla_clusterAttachment_of_avoidingAttachment ω x₁ ha1,
    cla_clusterAttachment_of_avoidingAttachment ω x₂ ha2,
    cla_clusterAttachment_of_avoidingAttachment ω x₃ ha3⟩




theorem cla_boxMengerAttachment_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : bmm_BoxMengerAttachment d n :=
  bma_boxMengerAttachment (cla_boxClusterAttachment_of_boxAvoiding h)





theorem cla_disjointRouting_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : hrHD_DisjointRouting d n :=
  bma_disjointRouting_of_clusterAttachment (cla_boxClusterAttachment_of_boxAvoiding h)











theorem cla_three_avoidingAttachments_of_neighbours (ω : ConfigSpace (Sym2 (Site d)))
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

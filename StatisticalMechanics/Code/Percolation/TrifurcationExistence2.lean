/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Percolation.BoxMergeFreeMenger

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}












def tex_ThreeDistinctInfinite (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ x₁ x₂ x₃ : Site d,
    ((cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite) ∧
    (cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)




theorem tex_threeDistinctInfinite_of_threeMeetBox {n : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    tex_ThreeDistinctInfinite ω := by
  obtain ⟨_, x₁, x₂, x₃, _, _, _, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  exact ⟨x₁, x₂, x₃, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩






















def tex_AttachData (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d) : Prop :=
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
      (cluster d (removeSite 0 ω) x₃).Infinite)




















theorem tex_insertion_of_attachData (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃) :
    tre_MergeFreeInsertion ω := by
  obtain ⟨hcd12, hcd13, hcd23⟩ := hd
  obtain ⟨a₁, a₂, a₃, W, hadj, hW, ⟨ha1, ha2, ha3⟩, ⟨hg1, hg2, hg3⟩,
    ⟨hc1, hc2, hc3⟩, ⟨hri1, hri2, hri3⟩⟩ := h
  
  have hdj12 : Disjoint (cluster d ω x₁) (cluster d ω x₂) := bmm_regions_disjoint ω hcd12
  have hdj13 : Disjoint (cluster d ω x₁) (cluster d ω x₃) := bmm_regions_disjoint ω hcd13
  have hdj23 : Disjoint (cluster d ω x₂) (cluster d ω x₃) := bmm_regions_disjoint ω hcd23
  
  have hne12 : a₁ ≠ a₂ := bmm_distinct_neighbours_of_disjoint_regions ha1 ha2 hdj12
  have hne13 : a₁ ≠ a₃ := bmm_distinct_neighbours_of_disjoint_regions ha1 ha3 hdj13
  have hne23 : a₂ ≠ a₃ := bmm_distinct_neighbours_of_disjoint_regions ha2 ha3 hdj23
  exact ⟨a₁, a₂, a₃, W, x₁, x₂, x₃, cluster d ω x₁, cluster d ω x₂, cluster d ω x₃,
    ⟨hne12, hne13, hne23⟩, hadj, hW, ⟨hc1, hc2, hc3⟩, ⟨hri1, hri2, hri3⟩,
    ⟨ha1, ha2, ha3⟩,
    ⟨bmm_cluster_omegaClosed ω x₁, bmm_cluster_omegaClosed ω x₂, bmm_cluster_omegaClosed ω x₃⟩,
    ⟨hg1, hg2, hg3⟩, ⟨hdj12, hdj13, hdj23⟩⟩














theorem tex_threeClustersReachOrigin (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tre_threeClustersReachOrigin_of_insertion ω (tex_insertion_of_attachData ω x₁ x₂ x₃ hd h)




theorem tex_mergeFree (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃) :
    ∃ W : Finset (Sym2 (Site d)), bka_MergeFree (forceOpenFinset W ω) := by
  obtain ⟨W, hreach⟩ := tex_threeClustersReachOrigin ω x₁ x₂ x₃ hd h
  exact ⟨W, mco_mergeFree (forceOpenFinset W ω) hreach⟩














def tex_BoxAttachData (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      tex_AttachData ω x₁ x₂ x₃





theorem tex_boxMengerAttachment_of_boxAttachData {n : ℕ}
    (h : tex_BoxAttachData d n) : bmm_BoxMengerAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23





theorem tex_threeClustersReachOrigin_of_box {n : ℕ}
    (h : tex_BoxAttachData d n) :
    ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  bmm_threeClustersReachOrigin_of_attachment (tex_boxMengerAttachment_of_boxAttachData h)





theorem tex_disjointRouting_of_box {n : ℕ}
    (h : tex_BoxAttachData d n) : hrHD_DisjointRouting d n :=
  bmm_disjointRouting_of_attachment (tex_boxMengerAttachment_of_boxAttachData h)






















theorem tex_attachData_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    tex_AttachData ω x₁ x₂ x₃ := by
  classical
  refine ⟨x₁, x₂, x₃, ∅, hadj, ?_, ?_, ?_, ?_, hri⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · exact ⟨self_mem_cluster ω x₁, self_mem_cluster ω x₂, self_mem_cluster ω x₃⟩
  · refine ⟨?_, ?_, ?_⟩ <;> (intro u v _ hW; exact absurd hW (Finset.notMem_empty _))
  · exact ⟨connected_rfl, connected_rfl, connected_rfl⟩






theorem tex_threeClustersReachOrigin_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ hd
    (tex_attachData_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri)





theorem tex_boxAttachData_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    tex_AttachData ω x₁ x₂ x₃ :=
  tex_attachData_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri

end Percolation

end StatMech

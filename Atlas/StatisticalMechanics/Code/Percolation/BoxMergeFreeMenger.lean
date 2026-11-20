/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Percolation.TrifurcationExistence

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}















theorem bmm_cluster_omegaClosed (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    ∀ u v, u ∈ cluster d ω x → IsOpenEdge d ω u v → v ∈ cluster d ω x := by
  intro u v hu hedge
  rw [mem_cluster] at hu ⊢
  exact hu.trans hedge.connected





theorem bmm_regions_disjoint (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hxy : cluster d ω x ≠ cluster d ω y) :
    Disjoint (cluster d ω x) (cluster d ω y) :=
  bcc_cluster_disjoint_of_ne ω x y hxy





theorem bmm_distinct_neighbours_of_disjoint_regions {a b : Site d} {R S : Set (Site d)}
    (ha : a ∈ R) (hb : b ∈ S) (hdisj : Disjoint R S) : a ≠ b := by
  intro he
  have hmem : a ∈ R ∩ S := ⟨ha, he ▸ hb⟩
  rw [Set.disjoint_iff_inter_eq_empty.mp hdisj] at hmem
  exact absurd hmem (Set.notMem_empty _)























def bmm_BoxMengerAttachment (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
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


























theorem bmm_boxMergeFreeInsertion_of_attachment {n : ℕ}
    (h : bmm_BoxMengerAttachment d n) : tre_BoxMergeFreeInsertion d n := by
  intro ω hω
  obtain ⟨hI, x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ := hω
  obtain ⟨a₁, a₂, a₃, W, hadj, hW, ⟨ha1, ha2, ha3⟩, ⟨hg1, hg2, hg3⟩,
    ⟨hc1, hc2, hc3⟩, ⟨hri1, hri2, hri3⟩⟩ :=
    h ω ⟨hI, x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩
      x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  
  have hd12 : Disjoint (cluster d ω x₁) (cluster d ω x₂) := bmm_regions_disjoint ω hcd12
  have hd13 : Disjoint (cluster d ω x₁) (cluster d ω x₃) := bmm_regions_disjoint ω hcd13
  have hd23 : Disjoint (cluster d ω x₂) (cluster d ω x₃) := bmm_regions_disjoint ω hcd23
  
  have hne12 : a₁ ≠ a₂ := bmm_distinct_neighbours_of_disjoint_regions ha1 ha2 hd12
  have hne13 : a₁ ≠ a₃ := bmm_distinct_neighbours_of_disjoint_regions ha1 ha3 hd13
  have hne23 : a₂ ≠ a₃ := bmm_distinct_neighbours_of_disjoint_regions ha2 ha3 hd23
  exact ⟨a₁, a₂, a₃, W, x₁, x₂, x₃, cluster d ω x₁, cluster d ω x₂, cluster d ω x₃,
    ⟨hne12, hne13, hne23⟩, hadj, hW, ⟨hc1, hc2, hc3⟩, ⟨hri1, hri2, hri3⟩,
    ⟨ha1, ha2, ha3⟩,
    ⟨bmm_cluster_omegaClosed ω x₁, bmm_cluster_omegaClosed ω x₂, bmm_cluster_omegaClosed ω x₃⟩,
    ⟨hg1, hg2, hg3⟩, ⟨hd12, hd13, hd23⟩⟩













theorem bmm_threeClustersReachOrigin_of_attachment {n : ℕ}
    (h : bmm_BoxMengerAttachment d n) :
    ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tre_threeClustersReachOrigin_of_finiteEnergy (bmm_boxMergeFreeInsertion_of_attachment h)





theorem bmm_disjointRouting_of_attachment {n : ℕ}
    (h : bmm_BoxMengerAttachment d n) : hrHD_DisjointRouting d n :=
  tre_disjointRouting_of_finiteEnergy (bmm_boxMergeFreeInsertion_of_attachment h)






















theorem bmm_attachment_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
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
  refine ⟨x₁, x₂, x₃, ∅, hadj, ?_, ?_, ?_, ?_, hri⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · exact ⟨self_mem_cluster ω x₁, self_mem_cluster ω x₂, self_mem_cluster ω x₃⟩
  · refine ⟨?_, ?_, ?_⟩ <;> (intro u v _ hW; exact absurd hW (Finset.notMem_empty _))
  · exact ⟨connected_rfl, connected_rfl, connected_rfl⟩

end Percolation

end StatMech

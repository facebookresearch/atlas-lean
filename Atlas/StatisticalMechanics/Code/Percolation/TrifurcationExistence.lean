/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Percolation.MengerCorridors

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}
















theorem tre_removeSite_forceOpen_comm (W : Finset (Sym2 (Site d)))
    (hW : ∀ e ∈ W, (0 : Site d) ∉ e) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite 0 (forceOpenFinset W ω) = forceOpenFinset W (removeSite 0 ω) := by
  funext e
  unfold removeSite forceOpenFinset
  by_cases hx : (0 : Site d) ∈ e
  · have hnW : e ∉ W := fun he => hW e he hx
    simp [hx, hnW]
  · by_cases heW : e ∈ W <;> simp [hx, heW]





theorem tre_removeSite_mono_forceOpen (W : Finset (Sym2 (Site d)))
    (hW : ∀ e ∈ W, (0 : Site d) ∉ e) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite 0 ω ≤ removeSite 0 (forceOpenFinset W ω) := by
  rw [tre_removeSite_forceOpen_comm W hW]
  exact forceOpenFinset_le W (removeSite 0 ω)











theorem tre_cluster_infinite_of_omega (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (hW : ∀ e ∈ W, (0 : Site d) ∉ e) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    (cluster d (removeSite 0 (forceOpenFinset W ω)) x).Infinite :=
  hinf.mono (cluster_mono (tre_removeSite_mono_forceOpen W hW ω) x)




theorem tre_branch_infinite_of_reach (ω' : ConfigSpace (Sym2 (Site d))) (a x : Site d)
    (hc : Connected d (removeSite 0 ω') a x)
    (hinf : (cluster d (removeSite 0 ω') x).Infinite) :
    (cluster d (removeSite 0 ω') a).Infinite := by
  rw [cluster_eq_of_connected hc]; exact hinf



















theorem tre_branch_distinct_of_regions (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (a b : Site d) (R S : Set (Site d))
    (haR : a ∈ R) (hbS : b ∈ S)
    (homR : ∀ u v, u ∈ R → IsOpenEdge d ω u v → v ∈ R)
    (hgR : ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R)
    (homS : ∀ u v, u ∈ S → IsOpenEdge d ω u v → v ∈ S)
    (hgS : ∀ u v, u ∈ S → s(u, v) ∈ W → v ∈ S)
    (hdisj : Disjoint R S) :
    cluster d (removeSite 0 (forceOpenFinset W ω)) a
      ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) b := by
  set ϱ := removeSite (0 : Site d) (forceOpenFinset W ω) with hϱ
  have hRcl : ∀ u v, u ∈ R → (openSubgraph d ϱ).Adj u v → v ∈ R :=
    bka_region_rhoAdjClosed ω W R homR hgR
  have hScl : ∀ u v, u ∈ S → (openSubgraph d ϱ).Adj u v → v ∈ S :=
    bka_region_rhoAdjClosed ω W S homS hgS
  have hsubR : cluster d ϱ a ⊆ R := DisjointPaths.cluster_subset_of_adjClosed ϱ R a haR hRcl
  have hsubS : cluster d ϱ b ⊆ S := DisjointPaths.cluster_subset_of_adjClosed ϱ S b hbS hScl
  exact DisjointPaths.cluster_ne_of_disjoint ϱ a b R S hsubR hsubS hdisj

























def tre_MergeFreeInsertion (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (R₁ R₂ R₃ : Set (Site d)),
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧
      Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧
      Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧
    ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧
      (cluster d (removeSite 0 ω) x₃).Infinite) ∧
    (a₁ ∈ R₁ ∧ a₂ ∈ R₂ ∧ a₃ ∈ R₃) ∧
    ((∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁) ∧
      (∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂) ∧
      (∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)) ∧
    ((∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁) ∧
      (∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂) ∧
      (∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)) ∧
    (Disjoint R₁ R₂ ∧ Disjoint R₁ R₃ ∧ Disjoint R₂ R₃)






















theorem tre_threeClustersReachOrigin_of_insertion (ω : ConfigSpace (Sym2 (Site d)))
    (h : tre_MergeFreeInsertion ω) :
    ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
  obtain ⟨a₁, a₂, a₃, W, x₁, x₂, x₃, R₁, R₂, R₃, hne, hadj, hW,
    ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hm1, hm2, hm3⟩,
    ⟨ho1, ho2, ho3⟩, ⟨hg1, hg2, hg3⟩, hd12, hd13, hd23⟩ := h
  refine ⟨W, a₁, a₂, a₃, x₁, x₂, x₃, hadj, ⟨hc1, hc2, hc3⟩, ?_, ?_⟩
  · 
    exact ⟨tre_cluster_infinite_of_omega ω W hW x₁ hi1,
      tre_cluster_infinite_of_omega ω W hW x₂ hi2,
      tre_cluster_infinite_of_omega ω W hW x₃ hi3⟩
  · 
    set ϱ := removeSite (0 : Site d) (forceOpenFinset W ω) with hϱ
    
    have ea1 : cluster d ϱ a₁ = cluster d ϱ x₁ := cluster_eq_of_connected hc1
    have ea2 : cluster d ϱ a₂ = cluster d ϱ x₂ := cluster_eq_of_connected hc2
    have ea3 : cluster d ϱ a₃ = cluster d ϱ x₃ := cluster_eq_of_connected hc3
    
    have nd12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂ :=
      tre_branch_distinct_of_regions ω W a₁ a₂ R₁ R₂ hm1 hm2 ho1 hg1 ho2 hg2 hd12
    have nd13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃ :=
      tre_branch_distinct_of_regions ω W a₁ a₃ R₁ R₃ hm1 hm3 ho1 hg1 ho3 hg3 hd13
    have nd23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃ :=
      tre_branch_distinct_of_regions ω W a₂ a₃ R₂ R₃ hm2 hm3 ho2 hg2 ho3 hg3 hd23
    refine ⟨?_, ?_, ?_⟩
    · rw [← ea1, ← ea2]; exact nd12
    · rw [← ea1, ← ea3]; exact nd13
    · rw [← ea2, ← ea3]; exact nd23










theorem tre_mergeFree_of_insertion (ω : ConfigSpace (Sym2 (Site d)))
    (h : tre_MergeFreeInsertion ω) :
    ∃ W : Finset (Sym2 (Site d)), bka_MergeFree (forceOpenFinset W ω) := by
  obtain ⟨W, hreach⟩ := tre_threeClustersReachOrigin_of_insertion ω h
  exact ⟨W, mco_mergeFree (forceOpenFinset W ω) hreach⟩























def tre_BoxMergeFreeInsertion (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
      (R₁ R₂ R₃ : Set (Site d)),
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃) ∧
      (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧
        Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧
        Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧
      ((cluster d (removeSite 0 ω) x₁).Infinite ∧
        (cluster d (removeSite 0 ω) x₂).Infinite ∧
        (cluster d (removeSite 0 ω) x₃).Infinite) ∧
      (a₁ ∈ R₁ ∧ a₂ ∈ R₂ ∧ a₃ ∈ R₃) ∧
      ((∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁) ∧
        (∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂) ∧
        (∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)) ∧
      ((∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁) ∧
        (∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂) ∧
        (∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)) ∧
      (Disjoint R₁ R₂ ∧ Disjoint R₁ R₃ ∧ Disjoint R₂ R₃)



theorem tre_insertion_of_boxResidue {n : ℕ} (h : tre_BoxMergeFreeInsertion d n)
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    tre_MergeFreeInsertion ω := h ω hω

















theorem tre_threeClustersReachOrigin_of_finiteEnergy {n : ℕ}
    (h : tre_BoxMergeFreeInsertion d n) :
    ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
  intro ω hω
  exact tre_threeClustersReachOrigin_of_insertion ω (tre_insertion_of_boxResidue h hω)















theorem tre_forceOpenFinset_comp (F W : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset F (forceOpenFinset W ω) = forceOpenFinset (F ∪ W) ω := by
  funext e
  unfold forceOpenFinset
  by_cases hF : e ∈ F
  · simp [hF, Finset.mem_union]
  · by_cases hW : e ∈ W <;> simp [hF, hW, Finset.mem_union]











theorem tre_precursor_of_modifiedMergeFree (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (h : bka_MergeFree (forceOpenFinset W ω)) :
    ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d),
      forceOpenFinset G ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃ := by
  classical
  set ωW := forceOpenFinset W ω with hωW
  obtain ⟨a₁, a₂, a₃, hne, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := h
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with hh | hh | hh <;> (rw [hh]; exact Sym2.mem_mk_left _ _)
  have hrm : removeSite (0:Site d) (forceOpenFinset F ωW) = removeSite (0:Site d) ωW :=
    removeSite_forceOpen_eq 0 F hFmem ωW
  refine ⟨F ∪ W, a₁, a₂, a₃, ?_⟩
  rw [← tre_forceOpenFinset_comp F W ω, ← hωW]
  refine ⟨hne, hadj, ?_, ?_, ?_, ?_⟩
  · rw [hrm]; exact ⟨hi1, hi2, hi3⟩
  · rw [hrm]; intro hc; exact hd12 (cluster_eq_of_connected hc)
  · rw [hrm]; intro hc; exact hd13 (cluster_eq_of_connected hc)
  · rw [hrm]; intro hc; exact hd23 (cluster_eq_of_connected hc)














theorem tre_disjointRouting_of_finiteEnergy {n : ℕ}
    (h : tre_BoxMergeFreeInsertion d n) : hrHD_DisjointRouting d n := by
  intro ω hω
  obtain ⟨W, hmf⟩ := tre_mergeFree_of_insertion ω (tre_insertion_of_boxResidue h hω)
  exact tre_precursor_of_modifiedMergeFree ω W hmf




















def tre_MergeFreeInsertionRho (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (R₁ R₂ R₃ : Set (Site d)),
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧
      Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧
      Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧
    ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧
      (cluster d (removeSite 0 ω) x₃).Infinite) ∧
    (a₁ ∈ R₁ ∧ a₂ ∈ R₂ ∧ a₃ ∈ R₃) ∧
    ((∀ u v, u ∈ R₁ → (openSubgraph d (removeSite 0 (forceOpenFinset W ω))).Adj u v → v ∈ R₁) ∧
      (∀ u v, u ∈ R₂ → (openSubgraph d (removeSite 0 (forceOpenFinset W ω))).Adj u v → v ∈ R₂) ∧
      (∀ u v, u ∈ R₃ → (openSubgraph d (removeSite 0 (forceOpenFinset W ω))).Adj u v → v ∈ R₃)) ∧
    (Disjoint R₁ R₂ ∧ Disjoint R₁ R₃ ∧ Disjoint R₂ R₃)





theorem tre_threeClustersReachOrigin_of_insertionRho (ω : ConfigSpace (Sym2 (Site d)))
    (h : tre_MergeFreeInsertionRho ω) :
    ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
  obtain ⟨a₁, a₂, a₃, W, x₁, x₂, x₃, R₁, R₂, R₃, hne, hadj, hW,
    ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hm1, hm2, hm3⟩,
    ⟨hcl1, hcl2, hcl3⟩, hd12, hd13, hd23⟩ := h
  set ϱ := removeSite (0 : Site d) (forceOpenFinset W ω) with hϱ
  refine ⟨W, a₁, a₂, a₃, x₁, x₂, x₃, hadj, ⟨hc1, hc2, hc3⟩, ?_, ?_⟩
  · exact ⟨tre_cluster_infinite_of_omega ω W hW x₁ hi1,
      tre_cluster_infinite_of_omega ω W hW x₂ hi2,
      tre_cluster_infinite_of_omega ω W hW x₃ hi3⟩
  · have ea1 : cluster d ϱ a₁ = cluster d ϱ x₁ := cluster_eq_of_connected hc1
    have ea2 : cluster d ϱ a₂ = cluster d ϱ x₂ := cluster_eq_of_connected hc2
    have ea3 : cluster d ϱ a₃ = cluster d ϱ x₃ := cluster_eq_of_connected hc3
    have hs1 : cluster d ϱ a₁ ⊆ R₁ := DisjointPaths.cluster_subset_of_adjClosed ϱ R₁ a₁ hm1 hcl1
    have hs2 : cluster d ϱ a₂ ⊆ R₂ := DisjointPaths.cluster_subset_of_adjClosed ϱ R₂ a₂ hm2 hcl2
    have hs3 : cluster d ϱ a₃ ⊆ R₃ := DisjointPaths.cluster_subset_of_adjClosed ϱ R₃ a₃ hm3 hcl3
    have nd12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂ :=
      DisjointPaths.cluster_ne_of_disjoint ϱ a₁ a₂ R₁ R₂ hs1 hs2 hd12
    have nd13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃ :=
      DisjointPaths.cluster_ne_of_disjoint ϱ a₁ a₃ R₁ R₃ hs1 hs3 hd13
    have nd23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃ :=
      DisjointPaths.cluster_ne_of_disjoint ϱ a₂ a₃ R₂ R₃ hs2 hs3 hd23
    exact ⟨by rw [← ea1, ← ea2]; exact nd12, by rw [← ea1, ← ea3]; exact nd13,
      by rw [← ea2, ← ea3]; exact nd23⟩












theorem tre_mergeFreeInsertionRho_of_reachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) : tre_MergeFreeInsertionRho ω := by
  classical
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hadj, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩,
    hd12, hd13, hd23⟩ := h
  set ϱ := removeSite (0 : Site d) ω with hϱ
  have hemp : forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := bka_forceOpenFinset_empty ω
  
  have hrm : removeSite (0 : Site d) (forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω) = ϱ := by
    rw [hemp]
  
  have ea1 : cluster d ϱ a₁ = cluster d ϱ x₁ := cluster_eq_of_connected hc1
  have ea2 : cluster d ϱ a₂ = cluster d ϱ x₂ := cluster_eq_of_connected hc2
  have ea3 : cluster d ϱ a₃ = cluster d ϱ x₃ := cluster_eq_of_connected hc3
  have nda12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂ := by rw [ea1, ea2]; exact hd12
  have nda13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃ := by rw [ea1, ea3]; exact hd13
  have nda23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃ := by rw [ea2, ea3]; exact hd23
  have hne12 : a₁ ≠ a₂ := fun he => nda12 (by rw [he])
  have hne13 : a₁ ≠ a₃ := fun he => nda13 (by rw [he])
  have hne23 : a₂ ≠ a₃ := fun he => nda23 (by rw [he])
  
  have hdisj : ∀ (b c : Site d), cluster d ϱ b ≠ cluster d ϱ c →
      Disjoint (cluster d ϱ b) (cluster d ϱ c) := by
    intro b c hbc
    rw [Set.disjoint_iff]
    rintro z ⟨hzb, hzc⟩
    rw [mem_cluster] at hzb hzc
    exact hbc ((cluster_eq_of_connected hzb).trans (cluster_eq_of_connected hzc).symm)
  refine ⟨a₁, a₂, a₃, ∅, a₁, a₂, a₃,
    cluster d ϱ a₁, cluster d ϱ a₂, cluster d ϱ a₃,
    ⟨hne12, hne13, hne23⟩, hadj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro e he; exact absurd he (Finset.notMem_empty e)
  · 
    rw [hrm]; exact ⟨connected_rfl, connected_rfl, connected_rfl⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · show (cluster d (removeSite 0 ω) a₁).Infinite
      rw [← hϱ, ea1]; exact hi1
    · show (cluster d (removeSite 0 ω) a₂).Infinite
      rw [← hϱ, ea2]; exact hi2
    · show (cluster d (removeSite 0 ω) a₃).Infinite
      rw [← hϱ, ea3]; exact hi3
  · 
    exact ⟨self_mem_cluster ϱ a₁, self_mem_cluster ϱ a₂, self_mem_cluster ϱ a₃⟩
  · 
    rw [hrm]
    exact ⟨bcc_cluster_adjClosed ϱ a₁, bcc_cluster_adjClosed ϱ a₂,
      bcc_cluster_adjClosed ϱ a₃⟩
  · 
    exact ⟨hdisj a₁ a₂ nda12, hdisj a₁ a₃ nda13, hdisj a₂ a₃ nda23⟩

end Percolation

end StatMech

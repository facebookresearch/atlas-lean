/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Percolation.TrifurcationExistence
import Code.Percolation.TrifurcationExistence2
import Code.Percolation.TrifurcationConstruction

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}













theorem tfe_threeMeetBox_of_top (ω : ConfigSpace (Sym2 (Site d)))
    (htop : numInfiniteClusters d ω = ⊤) :
    ∃ n : ℕ, ω ∈ threeMeetBox d n := by
  have hmem : ω ∈ ⋃ n, threeMeetBox d n :=
    iEqTop_subset_iUnion_threeMeetBox (by simpa using htop)
  rwa [Set.mem_iUnion] at hmem




theorem tfe_three_distinct_infinite_of_box {n : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁ x₂ x₃ : Site d, (x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n) ∧
      ((cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite) ∧
      (cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
        cluster d ω x₂ ≠ cluster d ω x₃) := by
  obtain ⟨_, x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  exact ⟨x₁, x₂, x₃, ⟨hb1, hb2, hb3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩




















theorem tfe_modification_preserves_distinct (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d) (R₁ R₂ R₃ : Set (Site d))
    (hm1 : a₁ ∈ R₁) (hm2 : a₂ ∈ R₂) (hm3 : a₃ ∈ R₃)
    (ho1 : ∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁)
    (ho2 : ∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂)
    (ho3 : ∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)
    (hg1 : ∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁)
    (hg2 : ∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂)
    (hg3 : ∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)
    (hd12 : Disjoint R₁ R₂) (hd13 : Disjoint R₁ R₃) (hd23 : Disjoint R₂ R₃) :
    (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₂) ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₂
        ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) :=
  ⟨tre_branch_distinct_of_regions ω W a₁ a₂ R₁ R₂ hm1 hm2 ho1 hg1 ho2 hg2 hd12,
    tre_branch_distinct_of_regions ω W a₁ a₃ R₁ R₃ hm1 hm3 ho1 hg1 ho3 hg3 hd13,
    tre_branch_distinct_of_regions ω W a₂ a₃ R₂ R₃ hm2 hm3 ho2 hg2 ho3 hg3 hd23⟩












theorem tfe_threeClustersReachOrigin_of_attach (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ hd h












def tfe_BoxAttachResidue (d n : ℕ) : Prop := tex_BoxAttachData d n












theorem tfe_threeClustersReachOrigin_of_top (ω : ConfigSpace (Sym2 (Site d)))
    (htop : numInfiniteClusters d ω = ⊤)
    (hres : ∀ m : ℕ, tfe_BoxAttachResidue d m) :
    ∃ (n : ℕ) (W : Finset (Sym2 (Site d))),
      ω ∈ threeMeetBox d n ∧ mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
  obtain ⟨n, hω⟩ := tfe_threeMeetBox_of_top ω htop
  obtain ⟨x₁, x₂, x₃, ⟨hb1, hb2, hb3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ :=
    tfe_three_distinct_infinite_of_box hω
  have hattach : tex_AttachData ω x₁ x₂ x₃ :=
    hres n ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23
  obtain ⟨W, hreach⟩ :=
    tfe_threeClustersReachOrigin_of_attach ω x₁ x₂ x₃ ⟨hd12, hd13, hd23⟩ hattach
  exact ⟨n, W, hω, hreach⟩






theorem tfe_routing_of_boxResidue {n : ℕ}
    (h : tfe_BoxAttachResidue d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box h













def tfe_TrifurcationContact (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite) ∧
    (cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃)




theorem tfe_reachOrigin_of_contact (ω : ConfigSpace (Sym2 (Site d)))
    (h : tfe_TrifurcationContact ω) : mco_ThreeClustersReachOrigin ω := by
  obtain ⟨a₁, a₂, a₃, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := h
  exact ⟨a₁, a₂, a₃, a₁, a₂, a₃, hadj,
    ⟨connected_rfl, connected_rfl, connected_rfl⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩





theorem tfe_contact_of_reachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) : tfe_TrifurcationContact ω := by
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hadj, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := h
  have e1 : cluster d (removeSite 0 ω) a₁ = cluster d (removeSite 0 ω) x₁ :=
    cluster_eq_of_connected hc1
  have e2 : cluster d (removeSite 0 ω) a₂ = cluster d (removeSite 0 ω) x₂ :=
    cluster_eq_of_connected hc2
  have e3 : cluster d (removeSite 0 ω) a₃ = cluster d (removeSite 0 ω) x₃ :=
    cluster_eq_of_connected hc3
  refine ⟨a₁, a₂, a₃, hadj, ⟨e1 ▸ hi1, e2 ▸ hi2, e3 ▸ hi3⟩, ?_, ?_, ?_⟩
  · rw [e1, e2]; exact hd12
  · rw [e1, e3]; exact hd13
  · rw [e2, e3]; exact hd23





theorem tfe_reachOrigin_iff_contact (ω : ConfigSpace (Sym2 (Site d))) :
    mco_ThreeClustersReachOrigin ω ↔ tfe_TrifurcationContact ω :=
  ⟨tfe_contact_of_reachOrigin ω, tfe_reachOrigin_of_contact ω⟩












theorem tfe_contact_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    tfe_TrifurcationContact ω :=
  ⟨a₁, a₂, a₃, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩




theorem tfe_reachOrigin_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    mco_ThreeClustersReachOrigin ω :=
  tfe_reachOrigin_of_contact ω
    (tfe_contact_of_neighbour_witnesses ω a₁ a₂ a₃ hadj hi1 hi2 hi3 hd12 hd13 hd23)





theorem tfe_attach_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    tex_AttachData ω x₁ x₂ x₃ :=
  tex_attachData_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri

end Percolation

end StatMech

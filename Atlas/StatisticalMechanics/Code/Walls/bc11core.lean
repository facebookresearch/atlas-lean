/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Walls.bc9core
import Code.Percolation.TrifurcationExistence
import Code.Percolation.TrifurcationExistence2
import Code.Percolation.BoxMergeFreeMenger
import Code.Percolation.CanonicalTrifCount
import Code.Percolation.LatticeMengerAttach
import Code.Walls.bc7distinctwitnessclusters

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory

namespace StatMech

namespace Walls

variable {d : ℕ}


































def bc11_BoxOriginOpenReach (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    ∃ y₁ y₂ y₃ : Site d, ∃ R₁ R₂ R₃ : Set (Site d),
      y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
      Connected d (forceOpenFinset W ω) 0 y₁ ∧
      Connected d (forceOpenFinset W ω) 0 y₂ ∧
      Connected d (forceOpenFinset W ω) 0 y₃ ∧
      (cluster d (removeSite 0 ω) y₁).Infinite ∧
      (cluster d (removeSite 0 ω) y₂).Infinite ∧
      (cluster d (removeSite 0 ω) y₃).Infinite ∧
      (y₁ ∈ R₁ ∧ y₂ ∈ R₂ ∧ y₃ ∈ R₃) ∧
      ((∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁) ∧
        (∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂) ∧
        (∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)) ∧
      ((∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁) ∧
        (∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂) ∧
        (∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)) ∧
      (Disjoint R₁ R₂ ∧ Disjoint R₁ R₃ ∧ Disjoint R₂ R₃)






















theorem bc11_boxOriginReach_of_openReach (n : ℕ) (h : bc11_BoxOriginOpenReach d n) :
    bc9_BoxOriginReach d n := by
  intro ω hω
  obtain ⟨W, hW0, y₁, y₂, y₃, R₁, R₂, R₃, hy1, hy2, hy3, hc1, hc2, hc3,
    hbi1, hbi2, hbi3, ⟨hm1, hm2, hm3⟩, ⟨ho1, ho2, ho3⟩, ⟨hg1, hg2, hg3⟩,
    hd12, hd13, hd23⟩ := h ω hω
  refine ⟨W, hW0, y₁, y₂, y₃, hy1, hy2, hy3, hc1, hc2, hc3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  
  · exact bc9_cutCluster_survives_infinite W ω hbi1
  · exact bc9_cutCluster_survives_infinite W ω hbi2
  · exact bc9_cutCluster_survives_infinite W ω hbi3
  
  · exact tre_branch_distinct_of_regions ω W y₁ y₂ R₁ R₂ hm1 hm2 ho1 hg1 ho2 hg2 hd12
  · exact tre_branch_distinct_of_regions ω W y₁ y₃ R₁ R₃ hm1 hm3 ho1 hg1 ho3 hg3 hd13
  · exact tre_branch_distinct_of_regions ω W y₂ y₃ R₂ R₃ hm2 hm3 ho2 hg2 ho3 hg3 hd23










theorem bc11_originRewiring_of_openReach (n : ℕ) (h : bc11_BoxOriginOpenReach d n) :
    bc8_OriginRewiring d n :=
  bc9_originRewiring_of_boxOriginReach n (bc11_boxOriginReach_of_openReach n h)





theorem bc11_canonicalTrif_of_openReach (n : ℕ) (h : bc11_BoxOriginOpenReach d n)
    (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n) :
    ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 :=
  bc9_canonicalTrif_of_boxOriginReach n (bc11_boxOriginReach_of_openReach n h) ω hω









theorem bc11_burtonKeane_uniqueness_of_openReach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hr : ∀ n : ℕ, bc11_BoxOriginOpenReach d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc9_burtonKeane_uniqueness_of_boxOriginReach μ herg hfe bdry hbound hvol hdens
    (fun n => bc11_boxOriginReach_of_openReach n (hr n))













theorem bc11_boxOriginOpenReach_of_reach (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (hW0 : ∀ e ∈ W, (0 : Site d) ∉ e)
    {y₁ y₂ y₃ : Site d} {R₁ R₂ R₃ : Set (Site d)}
    (hy1 : y₁ ≠ 0) (hy2 : y₂ ≠ 0) (hy3 : y₃ ≠ 0)
    (hc1 : Connected d (forceOpenFinset W ω) 0 y₁)
    (hc2 : Connected d (forceOpenFinset W ω) 0 y₂)
    (hc3 : Connected d (forceOpenFinset W ω) 0 y₃)
    (hbi1 : (cluster d (removeSite 0 ω) y₁).Infinite)
    (hbi2 : (cluster d (removeSite 0 ω) y₂).Infinite)
    (hbi3 : (cluster d (removeSite 0 ω) y₃).Infinite)
    (hm1 : y₁ ∈ R₁) (hm2 : y₂ ∈ R₂) (hm3 : y₃ ∈ R₃)
    (ho1 : ∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁)
    (ho2 : ∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂)
    (ho3 : ∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)
    (hg1 : ∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁)
    (hg2 : ∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂)
    (hg3 : ∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)
    (hd12 : Disjoint R₁ R₂) (hd13 : Disjoint R₁ R₃) (hd23 : Disjoint R₂ R₃) :
    ∃ W' : Finset (Sym2 (Site d)),
      (∀ e ∈ W', (0 : Site d) ∉ e) ∧
      ∃ z₁ z₂ z₃ : Site d, ∃ S₁ S₂ S₃ : Set (Site d),
        z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ z₃ ≠ 0 ∧
        Connected d (forceOpenFinset W' ω) 0 z₁ ∧
        Connected d (forceOpenFinset W' ω) 0 z₂ ∧
        Connected d (forceOpenFinset W' ω) 0 z₃ ∧
        (cluster d (removeSite 0 ω) z₁).Infinite ∧
        (cluster d (removeSite 0 ω) z₂).Infinite ∧
        (cluster d (removeSite 0 ω) z₃).Infinite ∧
        (z₁ ∈ S₁ ∧ z₂ ∈ S₂ ∧ z₃ ∈ S₃) ∧
        ((∀ u v, u ∈ S₁ → IsOpenEdge d ω u v → v ∈ S₁) ∧
          (∀ u v, u ∈ S₂ → IsOpenEdge d ω u v → v ∈ S₂) ∧
          (∀ u v, u ∈ S₃ → IsOpenEdge d ω u v → v ∈ S₃)) ∧
        ((∀ u v, u ∈ S₁ → s(u, v) ∈ W' → v ∈ S₁) ∧
          (∀ u v, u ∈ S₂ → s(u, v) ∈ W' → v ∈ S₂) ∧
          (∀ u v, u ∈ S₃ → s(u, v) ∈ W' → v ∈ S₃)) ∧
        (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃) :=
  ⟨W, hW0, y₁, y₂, y₃, R₁, R₂, R₃, hy1, hy2, hy3, hc1, hc2, hc3,
    hbi1, hbi2, hbi3, ⟨hm1, hm2, hm3⟩, ⟨ho1, ho2, ho3⟩, ⟨hg1, hg2, hg3⟩, hd12, hd13, hd23⟩




















theorem bc11_origin_openReach_needs_base_open_nbr (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (hW0 : ∀ e ∈ W, (0 : Site d) ∉ e) {y : Site d}
    (hy : y ≠ 0) (hconn : Connected d (forceOpenFinset W ω) 0 y) :
    ∃ v : Site d, (hypercubicLattice d).Adj 0 v ∧ ω s((0 : Site d), v) = true := by
  
  obtain ⟨w⟩ := hconn
  
  cases w with
  | nil => exact absurd rfl hy
  | @cons _ v _ hadj _ =>
    
    rw [openSubgraph_adj] at hadj
    obtain ⟨hlat, hopen⟩ := hadj
    
    have h0mem : (0 : Site d) ∈ s((0 : Site d), v) := Sym2.mem_mk_left 0 v
    have hnW : s((0 : Site d), v) ∉ W := fun he => hW0 _ he h0mem
    
    rw [forceOpenFinset_of_notMem hnW ω] at hopen
    exact ⟨v, hlat, hopen⟩














theorem bc11_isolated_origin_no_openReach (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (hW0 : ∀ e ∈ W, (0 : Site d) ∉ e)
    (hiso : ∀ v : Site d, ¬ (openSubgraph d ω).Adj 0 v)
    {y : Site d} (hy : y ≠ 0) (hconn : Connected d (forceOpenFinset W ω) 0 y) : False := by
  obtain ⟨v, hlat, hopen⟩ := bc11_origin_openReach_needs_base_open_nbr ω W hW0 hy hconn
  exact hiso v ⟨hlat, hopen⟩




























theorem bc11_boxReach_of_attachData_unpacked (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hadj1 : (hypercubicLattice d).Adj 0 a₁) (hadj2 : (hypercubicLattice d).Adj 0 a₂)
    (hadj3 : (hypercubicLattice d).Adj 0 a₃)
    (hW0 : ∀ e ∈ W, (0 : Site d) ∉ e)
    (ha1 : a₁ ∈ cluster d ω x₁) (ha2 : a₂ ∈ cluster d ω x₂) (ha3 : a₃ ∈ cluster d ω x₃)
    (hg1 : ∀ u v, u ∈ cluster d ω x₁ → s(u, v) ∈ W → v ∈ cluster d ω x₁)
    (hg2 : ∀ u v, u ∈ cluster d ω x₂ → s(u, v) ∈ W → v ∈ cluster d ω x₂)
    (hg3 : ∀ u v, u ∈ cluster d ω x₃ → s(u, v) ∈ W → v ∈ cluster d ω x₃)
    (hcr1 : Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁)
    (hcr2 : Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂)
    (hcr3 : Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃)
    (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite)
    (hd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    
    (ho1 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁)
    (ho2 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂)
    (ho3 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃) :
    ∃ W' : Finset (Sym2 (Site d)),
      (∀ e ∈ W', (0 : Site d) ∉ e) ∧
      ∃ y₁ y₂ y₃ : Site d,
        y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
        Connected d (forceOpenFinset W' ω) 0 y₁ ∧
        Connected d (forceOpenFinset W' ω) 0 y₂ ∧
        Connected d (forceOpenFinset W' ω) 0 y₃ ∧
        (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃).Infinite ∧
        cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂ ∧
        cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃ ∧
        cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂ ≠
          cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃ := by
  set ϱ := removeSite (0 : Site d) (forceOpenFinset W ω) with hϱ
  
  have hxi1 : (cluster d ϱ x₁).Infinite := bc9_cutCluster_survives_infinite W ω hi1
  have hxi2 : (cluster d ϱ x₂).Infinite := bc9_cutCluster_survives_infinite W ω hi2
  have hxi3 : (cluster d ϱ x₃).Infinite := bc9_cutCluster_survives_infinite W ω hi3
  have eai1 : cluster d ϱ a₁ = cluster d ϱ x₁ := cluster_eq_of_connected hcr1
  have eai2 : cluster d ϱ a₂ = cluster d ϱ x₂ := cluster_eq_of_connected hcr2
  have eai3 : cluster d ϱ a₃ = cluster d ϱ x₃ := cluster_eq_of_connected hcr3
  
  have hdj12 : Disjoint (cluster d ω x₁) (cluster d ω x₂) := bmm_regions_disjoint ω hd12
  have hdj13 : Disjoint (cluster d ω x₁) (cluster d ω x₃) := bmm_regions_disjoint ω hd13
  have hdj23 : Disjoint (cluster d ω x₂) (cluster d ω x₃) := bmm_regions_disjoint ω hd23
  have nd12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂ :=
    tre_branch_distinct_of_regions ω W a₁ a₂ (cluster d ω x₁) (cluster d ω x₂)
      ha1 ha2 (bmm_cluster_omegaClosed ω x₁) hg1 (bmm_cluster_omegaClosed ω x₂) hg2 hdj12
  have nd13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃ :=
    tre_branch_distinct_of_regions ω W a₁ a₃ (cluster d ω x₁) (cluster d ω x₃)
      ha1 ha3 (bmm_cluster_omegaClosed ω x₁) hg1 (bmm_cluster_omegaClosed ω x₃) hg3 hdj13
  have nd23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃ :=
    tre_branch_distinct_of_regions ω W a₂ a₃ (cluster d ω x₂) (cluster d ω x₃)
      ha2 ha3 (bmm_cluster_omegaClosed ω x₂) hg2 (bmm_cluster_omegaClosed ω x₃) hg3 hdj23
  refine ⟨W, hW0, a₁, a₂, a₃, (hadj1.ne).symm, (hadj2.ne).symm, (hadj3.ne).symm,
    ho1.reachable, ho2.reachable, ho3.reachable, ?_, ?_, ?_, nd12, nd13, nd23⟩
  · rw [eai1]; exact hxi1
  · rw [eai2]; exact hxi2
  · rw [eai3]; exact hxi3











theorem bc11_boxReach_of_attachData (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃)
    
    (hopen : ∀ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))),
      (∀ e ∈ W, (0 : Site d) ∉ e) →
      (hypercubicLattice d).Adj 0 a₁ → (hypercubicLattice d).Adj 0 a₂ →
      (hypercubicLattice d).Adj 0 a₃ →
      a₁ ∈ cluster d ω x₁ → a₂ ∈ cluster d ω x₂ → a₃ ∈ cluster d ω x₃ →
      (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁ ∧
        (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂ ∧
        (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃) :
    ∃ W' : Finset (Sym2 (Site d)),
      (∀ e ∈ W', (0 : Site d) ∉ e) ∧
      ∃ y₁ y₂ y₃ : Site d,
        y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
        Connected d (forceOpenFinset W' ω) 0 y₁ ∧
        Connected d (forceOpenFinset W' ω) 0 y₂ ∧
        Connected d (forceOpenFinset W' ω) 0 y₃ ∧
        (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃).Infinite ∧
        cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂ ∧
        cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃ ∧
        cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂ ≠
          cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃ := by
  obtain ⟨a₁, a₂, a₃, W, hadj, hW0, ⟨ha1, ha2, ha3⟩, ⟨hg1, hg2, hg3⟩,
    ⟨hcr1, hcr2, hcr3⟩, ⟨hi1, hi2, hi3⟩⟩ := h
  obtain ⟨hadj1, hadj2, hadj3⟩ := hadj
  obtain ⟨ho1, ho2, ho3⟩ := hopen a₁ a₂ a₃ W hW0 hadj1 hadj2 hadj3 ha1 ha2 ha3
  exact bc11_boxReach_of_attachData_unpacked ω a₁ a₂ a₃ W x₁ x₂ x₃
    hadj1 hadj2 hadj3 hW0 ha1 ha2 ha3 hg1 hg2 hg3 hcr1 hcr2 hcr3 hi1 hi2 hi3
    hd12 hd13 hd23 ho1 ho2 ho3



















def bc11_BoxOriginOpenIncidence (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      ∀ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))),
        (∀ e ∈ W, (0 : Site d) ∉ e) →
        (hypercubicLattice d).Adj 0 a₁ → (hypercubicLattice d).Adj 0 a₂ →
        (hypercubicLattice d).Adj 0 a₃ →
        a₁ ∈ cluster d ω x₁ → a₂ ∈ cluster d ω x₂ → a₃ ∈ cluster d ω x₃ →
        (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁ ∧
          (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂ ∧
          (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃












theorem bc11_boxOriginReach_of_attachData_and_openIncidence (n : ℕ)
    (hattach : tex_BoxAttachData d n) (hinc : bc11_BoxOriginOpenIncidence d n) :
    bc9_BoxOriginReach d n := by
  intro ω hω
  
  obtain ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23,
      _x₁', _x₂', _x₃', _, _, _, _, _, _, _, _, _⟩ :=
    bc7_distinctWitnessClusters n ω hω
  
  have hAttach : tex_AttachData ω x₁ x₂ x₃ :=
    hattach ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23
  
  exact bc11_boxReach_of_attachData ω x₁ x₂ x₃ hd12 hd13 hd23 hAttach
    (fun a₁ a₂ a₃ W hW0 hadj1 hadj2 hadj3 ha1 ha2 ha3 =>
      hinc ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23
        a₁ a₂ a₃ W hW0 hadj1 hadj2 hadj3 ha1 ha2 ha3)





theorem bc11_originRewiring_of_attachData_and_openIncidence (n : ℕ)
    (hattach : tex_BoxAttachData d n) (hinc : bc11_BoxOriginOpenIncidence d n) :
    bc8_OriginRewiring d n :=
  bc9_originRewiring_of_boxOriginReach n
    (bc11_boxOriginReach_of_attachData_and_openIncidence n hattach hinc)



section AxiomAudit


#guard_msgs in
#print axioms bc11_boxOriginReach_of_openReach


#guard_msgs in
#print axioms bc11_originRewiring_of_openReach


#guard_msgs in
#print axioms bc11_burtonKeane_uniqueness_of_openReach


#guard_msgs in
#print axioms bc11_boxOriginOpenReach_of_reach


#guard_msgs in
#print axioms bc11_origin_openReach_needs_base_open_nbr


#guard_msgs in
#print axioms bc11_isolated_origin_no_openReach


#guard_msgs in
#print axioms bc11_boxReach_of_attachData


#guard_msgs(whitespace := lax) in
#print axioms bc11_boxOriginReach_of_attachData_and_openIncidence


#guard_msgs(whitespace := lax) in
#print axioms bc11_originRewiring_of_attachData_and_openIncidence

end AxiomAudit

end Walls

end StatMech

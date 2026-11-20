/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Walls.bc95forestdensity
import Code.Walls.bc87prune
import Code.Percolation.TrifurcationExistence
import Code.Percolation.HrouteDisjointPaths

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


























theorem bc96_genuineTrif_of_reachOrigin_full (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ x₁ x₂ x₃ : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hconn : Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧
      Connected d (removeSite 0 ω) a₃ x₃)
    (hinf : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite)
    (hdist : cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
      cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃)
    (hopen : ω s(0, a₁) = true ∧ ω s(0, a₂) = true ∧ ω s(0, a₃) = true) :
    bc89_GenuineTrif d ω 0 := by
  obtain ⟨hadj1, hadj2, hadj3⟩ := hadj
  obtain ⟨hc1, hc2, hc3⟩ := hconn
  obtain ⟨hi1, hi2, hi3⟩ := hinf
  obtain ⟨hd12, hd13, hd23⟩ := hdist
  obtain ⟨ho1, ho2, ho3⟩ := hopen
  
  have ea1 : cluster d (removeSite 0 ω) a₁ = cluster d (removeSite 0 ω) x₁ :=
    cluster_eq_of_connected hc1
  have ea2 : cluster d (removeSite 0 ω) a₂ = cluster d (removeSite 0 ω) x₂ :=
    cluster_eq_of_connected hc2
  have ea3 : cluster d (removeSite 0 ω) a₃ = cluster d (removeSite 0 ω) x₃ :=
    cluster_eq_of_connected hc3
  
  have nd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ := by
    rw [ea1, ea2]; exact hd12
  have nd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ := by
    rw [ea1, ea3]; exact hd13
  have nd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃ := by
    rw [ea2, ea3]; exact hd23
  
  have hne12 : a₁ ≠ a₂ := fun hh => nd12 (by rw [hh])
  have hne13 : a₁ ≠ a₃ := fun hh => nd13 (by rw [hh])
  have hne23 : a₂ ≠ a₃ := fun hh => nd23 (by rw [hh])
  
  have hnx1 : a₁ ≠ (0 : Site d) := fun hh => hadj1.ne' (by rw [hh])
  have hnx2 : a₂ ≠ (0 : Site d) := fun hh => hadj2.ne' (by rw [hh])
  have hnx3 : a₃ ≠ (0 : Site d) := fun hh => hadj3.ne' (by rw [hh])
  
  have hai1 : (cluster d (removeSite 0 ω) a₁).Infinite := by rw [ea1]; exact hi1
  have hai2 : (cluster d (removeSite 0 ω) a₂).Infinite := by rw [ea2]; exact hi2
  have hai3 : (cluster d (removeSite 0 ω) a₃).Infinite := by rw [ea3]; exact hi3
  
  have hsep12 : ¬ Connected d (removeSite 0 ω) a₁ a₂ :=
    fun hh => nd12 (cluster_eq_of_connected hh)
  have hsep13 : ¬ Connected d (removeSite 0 ω) a₁ a₃ :=
    fun hh => nd13 (cluster_eq_of_connected hh)
  have hsep23 : ¬ Connected d (removeSite 0 ω) a₂ a₃ :=
    fun hh => nd23 (cluster_eq_of_connected hh)
  
  refine ⟨a₁, a₂, a₃, ⟨hne12, hne13, hne23⟩, ⟨hnx1, hnx2, hnx3⟩,
    ⟨⟨hadj1, ho1⟩, ⟨hadj2, ho2⟩, ⟨hadj3, ho3⟩⟩,
    ⟨hai1, hai2, hai3⟩, ⟨hsep12, hsep13, hsep23⟩⟩













theorem bc96_measurableSet_openAdj (x a : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x a} := by
  by_cases hadj : (hypercubicLattice d).Adj x a
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x a}
        = (fun ω => ω s(x, a)) ⁻¹' {true} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, openSubgraph_adj]
      exact ⟨fun hh => hh.2, fun hh => ⟨hadj, hh⟩⟩
    rw [heq]
    exact (measurable_pi_apply (s(x, a) : Sym2 (Site d))) (measurableSet_singleton true)
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x a} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, openSubgraph_adj, Set.mem_empty_iff_false, iff_false]
      exact fun hh => hadj hh.1
    rw [heq]; exact MeasurableSet.empty



theorem bc96_measurableSet_removeSite_clusterInfinite (x a : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | (cluster d ω' a).Infinite} := rfl
  rw [h]
  exact (measurable_removeSite x) (measurableSet_clusterInfinite a)






theorem bc96_measurableSet_genuineTrif (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | bc89_GenuineTrif d ω x} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | bc89_GenuineTrif d ω x}
      = ⋃ a₁ : Site d, ⋃ a₂ : Site d, ⋃ a₃ : Site d,
          ((if (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (a₁ ≠ x ∧ a₂ ≠ x ∧ a₃ ≠ x)
              then Set.univ else ∅)
            ∩ ({ω | (openSubgraph d ω).Adj x a₁} ∩ {ω | (openSubgraph d ω).Adj x a₂}
                ∩ {ω | (openSubgraph d ω).Adj x a₃})
            ∩ ({ω | (cluster d (removeSite x ω) a₁).Infinite}
                ∩ {ω | (cluster d (removeSite x ω) a₂).Infinite}
                ∩ {ω | (cluster d (removeSite x ω) a₃).Infinite})
            ∩ ({ω | ¬ Connected d (removeSite x ω) a₁ a₂}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₁ a₃}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₂ a₃})) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨a₁, a₂, a₃, hne, hnx, hadj, hinf, hsep⟩
      refine ⟨a₁, a₂, a₃, ⟨⟨⟨?_, ⟨⟨hadj.1, hadj.2.1⟩, hadj.2.2⟩⟩,
        ⟨⟨hinf.1, hinf.2.1⟩, hinf.2.2⟩⟩, ⟨⟨hsep.1, hsep.2.1⟩, hsep.2.2⟩⟩⟩
      rw [if_pos ⟨hne, hnx⟩]; exact Set.mem_univ _
    · rintro ⟨a₁, a₂, a₃, ⟨⟨⟨hif, ⟨⟨ha1, ha2⟩, ha3⟩⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩⟩
      by_cases hh : (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (a₁ ≠ x ∧ a₂ ≠ x ∧ a₃ ≠ x)
      · exact ⟨a₁, a₂, a₃, hh.1, hh.2, ⟨ha1, ha2, ha3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
      · rw [if_neg hh] at hif; exact absurd hif (Set.notMem_empty _)
  rw [heq]
  refine MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
    MeasurableSet.iUnion fun a₃ => ?_
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  · by_cases hh : (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (a₁ ≠ x ∧ a₂ ≠ x ∧ a₃ ≠ x)
    · rw [if_pos hh]; exact MeasurableSet.univ
    · rw [if_neg hh]; exact MeasurableSet.empty
  · exact ((bc96_measurableSet_openAdj x a₁).inter (bc96_measurableSet_openAdj x a₂)).inter
      (bc96_measurableSet_openAdj x a₃)
  · exact ((bc96_measurableSet_removeSite_clusterInfinite x a₁).inter
      (bc96_measurableSet_removeSite_clusterInfinite x a₂)).inter
      (bc96_measurableSet_removeSite_clusterInfinite x a₃)
  · exact (((measurableSet_connected_removeSite x a₁ a₂).compl).inter
      ((measurableSet_connected_removeSite x a₁ a₃).compl)).inter
      ((measurableSet_connected_removeSite x a₂ a₃).compl)



















theorem bc96_singleSiteRewiring_of_precursor
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hpre : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ (G : Finset (Sym2 (Site d))) (A : Set (ConfigSpace (Sym2 (Site d)))),
        0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif d ω 0}) :
    bc95_SingleSiteRewiring μ := by
  intro hpos
  obtain ⟨G, A, hApos, hAsub⟩ := hpre hpos
  have htgt : 0 < μ {ω | bc89_GenuineTrif d ω 0} :=
    DisjointPaths.pos_of_forceOpen_preimage μ hfe G (bc96_measurableSet_genuineTrif 0) hAsub hApos
  exact ⟨{ω | bc89_GenuineTrif d ω 0}, htgt, subset_rfl⟩








theorem bc96_bk_from_precursor
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (hpre : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ (G : Finset (Sym2 (Site d))) (A : Set (ConfigSpace (Sym2 (Site d)))),
        0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif d ω 0}) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc95_bk_from_residues μ hprob0 (bc96_singleSiteRewiring_of_precursor μ hfe hpre)

















theorem bc96_arm_reaches_boundary_perConfig (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d)
    (hinf : (cluster d (removeSite x ω) a).Infinite) (n : ℕ) :
    ∃ z, z ∉ box d n ∧ Connected d (removeSite x ω) a z :=
  (cluster_infinite_iff (removeSite x ω) a).mp hinf n





theorem bc96_harmbox_free_of_interior (ω : ConfigSpace (Sym2 (Site d))) {n : ℕ} (hn : 1 ≤ n)
    {x : Site d} (hxint : x ∈ box d (n - 1))
    {a : Site d} (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d n :=
  bc90_harmbox_free_of_interior ω hn hxint hadj










theorem bc96_harmbox_not_perConfig (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hadj : (openSubgraph d ω).Adj x a)
    (hinf : (cluster d (removeSite x ω) a).Infinite) (hout : a ∉ box d n) :
    ¬ (∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ∀ b, (openSubgraph d ω).Adj y b → (cluster d (removeSite y ω) b).Infinite → b ∈ box d n) := by
  intro hharm
  exact hout (hharm x hxbox htri a hadj hinf)












theorem bc96_genuineTrif_of_mco (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω)
    (hopen : ∀ a : Site d, (hypercubicLattice d).Adj 0 a →
      (∃ x, Connected d (removeSite 0 ω) a x ∧ (cluster d (removeSite 0 ω) x).Infinite) →
      ω s(0, a) = true) :
    bc89_GenuineTrif d ω 0 := by
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hadj, hconn, hinf, hdist⟩ := h
  refine bc96_genuineTrif_of_reachOrigin_full ω hadj hconn hinf hdist ?_
  refine ⟨hopen a₁ hadj.1 ⟨_, hconn.1, hinf.1⟩,
    hopen a₂ hadj.2.1 ⟨_, hconn.2.1, hinf.2.1⟩,
    hopen a₃ hadj.2.2 ⟨_, hconn.2.2, hinf.2.2⟩⟩































theorem bc96_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2},
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) →
      (Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
        Connected 2 (removeSite 0 ω) a₃ x₃) →
      ((cluster 2 (removeSite 0 ω) x₁).Infinite ∧ (cluster 2 (removeSite 0 ω) x₂).Infinite ∧
        (cluster 2 (removeSite 0 ω) x₃).Infinite) →
      (cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₂ ∧
        cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₃ ∧
        cluster 2 (removeSite 0 ω) x₂ ≠ cluster 2 (removeSite 0 ω) x₃) →
      (ω s(0, a₁) = true ∧ ω s(0, a₂) = true ∧ ω s(0, a₃) = true) →
      bc89_GenuineTrif 2 ω 0) ∧
    
    (MeasurableSet {ω : ConfigSpace (Sym2 (Site 2)) | bc89_GenuineTrif 2 ω 0}) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ →
      (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
        ∃ (G : Finset (Sym2 (Site 2))) (A : Set (ConfigSpace (Sym2 (Site 2)))),
          0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif 2 ω 0}) →
      bc95_SingleSiteRewiring μ) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2),
      (cluster 2 (removeSite x ω) a).Infinite → ∀ n : ℕ,
      ∃ z, z ∉ box 2 n ∧ Connected 2 (removeSite x ω) a z) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ → μ {ω | bc89_GenuineTrif 2 ω 0} = 0 →
      (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
        ∃ (G : Finset (Sym2 (Site 2))) (A : Set (ConfigSpace (Sym2 (Site 2)))),
          0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif 2 ω 0}) →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω a₁ a₂ a₃ x₁ x₂ x₃ hadj hconn hinf hdist hopen
    exact bc96_genuineTrif_of_reachOrigin_full ω hadj hconn hinf hdist hopen
  · exact bc96_measurableSet_genuineTrif 0
  · intro μ _ hfe hpre; exact bc96_singleSiteRewiring_of_precursor μ hfe hpre
  · intro ω x a hinf n; exact bc96_arm_reaches_boundary_perConfig ω x a hinf n
  · intro μ _ hfe hprob0 hpre; exact bc96_bk_from_precursor μ hfe hprob0 hpre

end StatMech.Walls

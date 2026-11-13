/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Walls.bc97precursor
import Code.Percolation.TrifurcationFiniteEnergy
import Code.Percolation.TrifurcationExistence2

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










theorem bc98_mem_precursor_iff (ω : ConfigSpace (Sym2 (Site d))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site d) :
    ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ ↔
      (((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
          (hypercubicLattice d).Adj 0 a₃) ∧
        (Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧
          Connected d (removeSite 0 ω) a₃ x₃) ∧
        ((cluster d (removeSite 0 ω) x₁).Infinite ∧
          (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) ∧
        (cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
          cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
          cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃)) :=
  Iff.rfl





theorem bc98_mco_iff_exists_precursor (ω : ConfigSpace (Sym2 (Site d))) :
    mco_ThreeClustersReachOrigin ω ↔
      ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ := by
  constructor
  · rintro ⟨a₁, a₂, a₃, x₁, x₂, x₃, h⟩
    exact ⟨a₁, a₂, a₃, x₁, x₂, x₃, (bc98_mem_precursor_iff ω a₁ a₂ a₃ x₁ x₂ x₃).mpr h⟩
  · rintro ⟨a₁, a₂, a₃, x₁, x₂, x₃, h⟩
    exact ⟨a₁, a₂, a₃, x₁, x₂, x₃, (bc98_mem_precursor_iff ω a₁ a₂ a₃ x₁ x₂ x₃).mp h⟩














theorem bc98_measurableSet_singleSitePrecursor (a₁ a₂ a₃ x₁ x₂ x₃ : Site d) :
    MeasurableSet (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃) := by
  classical
  
  have hne_eq : ∀ (u v : Site d),
      {ω : ConfigSpace (Sym2 (Site d)) |
          cluster d (removeSite 0 ω) u ≠ cluster d (removeSite 0 ω) v}
        = {ω | ¬ Connected d (removeSite 0 ω) u v} := by
    intro u v
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hne hc; exact hne (cluster_eq_of_connected hc)
    · intro hnc heq
      have hv : v ∈ cluster d (removeSite 0 ω) u := by
        rw [heq]; exact self_mem_cluster _ v
      exact hnc (mem_cluster.mp hv)
  have heq : bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃
      = (if ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
              (hypercubicLattice d).Adj 0 a₃) then Set.univ else ∅)
          ∩ ({ω | Connected d (removeSite 0 ω) a₁ x₁} ∩
              {ω | Connected d (removeSite 0 ω) a₂ x₂} ∩
              {ω | Connected d (removeSite 0 ω) a₃ x₃})
          ∩ ({ω | (cluster d (removeSite 0 ω) x₁).Infinite} ∩
              {ω | (cluster d (removeSite 0 ω) x₂).Infinite} ∩
              {ω | (cluster d (removeSite 0 ω) x₃).Infinite})
          ∩ ({ω | cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂} ∩
              {ω | cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃} ∩
              {ω | cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃}) := by
    ext ω
    simp only [bc97_SingleSitePrecursor, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hadj, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hd12, hd13, hd23⟩⟩
      refine ⟨⟨⟨?_, ⟨⟨hc1, hc2⟩, hc3⟩⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hd12, hd13⟩, hd23⟩⟩
      rw [if_pos hadj]; exact Set.mem_univ _
    · rintro ⟨⟨⟨hif, ⟨⟨hc1, hc2⟩, hc3⟩⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hd12, hd13⟩, hd23⟩⟩
      by_cases hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
          (hypercubicLattice d).Adj 0 a₃
      · exact ⟨hadj, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hd12, hd13, hd23⟩⟩
      · rw [if_neg hadj] at hif; exact absurd hif (Set.notMem_empty _)
  rw [heq]
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  · by_cases hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃
    · rw [if_pos hadj]; exact MeasurableSet.univ
    · rw [if_neg hadj]; exact MeasurableSet.empty
  · exact ((measurableSet_connected_removeSite 0 a₁ x₁).inter
      (measurableSet_connected_removeSite 0 a₂ x₂)).inter
      (measurableSet_connected_removeSite 0 a₃ x₃)
  · exact ((DisjointPaths.measurableSet_clusterInfinite_removeSite 0 x₁).inter
      (DisjointPaths.measurableSet_clusterInfinite_removeSite 0 x₂)).inter
      (DisjointPaths.measurableSet_clusterInfinite_removeSite 0 x₃)
  · rw [hne_eq x₁ x₂, hne_eq x₁ x₃, hne_eq x₂ x₃]
    exact (((measurableSet_connected_removeSite 0 x₁ x₂).compl).inter
      ((measurableSet_connected_removeSite 0 x₁ x₃).compl)).inter
      ((measurableSet_connected_removeSite 0 x₂ x₃).compl)














theorem bc98_boxRoute_of_attach {n : ℕ} (hres : tex_BoxAttachData d n)
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    ∃ (a₁ a₂ a₃ x₁ x₂ x₃ : Site d) (W : Finset (Sym2 (Site d))),
      forceOpenFinset W ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ := by
  obtain ⟨y₁, y₂, y₃, ⟨hb1, hb2, hb3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ :=
    tfe_three_distinct_infinite_of_box hω
  have hattach : tex_AttachData ω y₁ y₂ y₃ :=
    hres ω hω y₁ y₂ y₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23
  obtain ⟨W, hreach⟩ := tex_threeClustersReachOrigin ω y₁ y₂ y₃ ⟨hd12, hd13, hd23⟩ hattach
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hmem⟩ :=
    (bc98_mco_iff_exists_precursor (forceOpenFinset W ω)).mp hreach
  exact ⟨a₁, a₂, a₃, x₁, x₂, x₃, W, hmem⟩





theorem bc98_precursorCover_of_attach {n : ℕ} (hres : tex_BoxAttachData d n) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (x₁ : Site d) (x₂ : Site d) (x₃ : Site d)
        (W : Finset (Sym2 (Site d))),
        (fun ω => forceOpenFinset W ω) ⁻¹' bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ := by
  intro ω hω
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, W, hmem⟩ := bc98_boxRoute_of_attach hres hω
  simp only [Set.mem_iUnion, Set.mem_preimage]
  exact ⟨a₁, a₂, a₃, x₁, x₂, x₃, W, hmem⟩













theorem bc98_hroute_at_of_attach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) {n : ℕ} (hres : tex_BoxAttachData d n)
    (hpos : 0 < μ (threeMeetBox d n)) :
    ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, 0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃) := by
  classical
  
  set ι := Site d × Site d × Site d × Site d × Site d × Site d × Finset (Sym2 (Site d)) with hι
  set B : ι → Set (ConfigSpace (Sym2 (Site d))) :=
    fun p => (fun ω => forceOpenFinset p.2.2.2.2.2.2 ω) ⁻¹'
      bc97_SingleSitePrecursor d p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 with hB
  have hcover : threeMeetBox d n ⊆ ⋃ p : ι, B p := by
    intro ω hω
    obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, W, hmem⟩ := by
      have := bc98_precursorCover_of_attach hres hω
      simpa only [Set.mem_iUnion] using this
    exact Set.mem_iUnion.mpr ⟨(a₁, a₂, a₃, x₁, x₂, x₃, W), hmem⟩
  
  obtain ⟨p, hppos⟩ := DisjointPaths.exists_pos_of_cover μ hcover hpos
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, W⟩ := p
  
  refine ⟨a₁, a₂, a₃, x₁, x₂, x₃, ?_⟩
  exact DisjointPaths.pos_of_forceOpen_preimage μ hfe W
    (bc98_measurableSet_singleSitePrecursor a₁ a₂ a₃ x₁ x₂ x₃)
    (subset_rfl) hppos










theorem bc98_hroute_of_boxAttach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (hres : ∀ n : ℕ, tex_BoxAttachData d n) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d,
        0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃) := by
  intro hpos
  obtain ⟨n, hnpos⟩ := exists_threeMeetBox_pos μ hpos
  exact bc98_hroute_at_of_attach μ hfe (hres n) hnpos







theorem bc98_close_a_of_boxAttach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (hres : ∀ n : ℕ, tex_BoxAttachData d n) :
    bc95_SingleSiteRewiring μ :=
  bc97_close_a μ hfe (bc98_hroute_of_boxAttach μ hfe hres)









theorem bc98_bk_from_boxAttach
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (hres : ∀ n : ℕ, tex_BoxAttachData d n) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc95_bk_from_residues μ hprob0 (bc98_close_a_of_boxAttach μ hfe hres)
















theorem bc98_precursor_of_contact (ω : ConfigSpace (Sym2 (Site d)))
    (h : tfe_TrifurcationContact ω) :
    ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ :=
  (bc98_mco_iff_exists_precursor ω).mp (tfe_reachOrigin_of_contact ω h)





























theorem bc98_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))),
      mco_ThreeClustersReachOrigin ω ↔
        ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2, ω ∈ bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃) ∧
    
    (∀ (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2),
      MeasurableSet (bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃)) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ → (∀ n : ℕ, tex_BoxAttachData 2 n) →
      0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
        ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2,
          0 < μ (bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃)) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ → (∀ n : ℕ, tex_BoxAttachData 2 n) →
      bc95_SingleSiteRewiring μ) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ → μ {ω | bc89_GenuineTrif 2 ω 0} = 0 →
      (∀ n : ℕ, tex_BoxAttachData 2 n) →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω; exact bc98_mco_iff_exists_precursor ω
  · intro a₁ a₂ a₃ x₁ x₂ x₃; exact bc98_measurableSet_singleSitePrecursor a₁ a₂ a₃ x₁ x₂ x₃
  · intro μ _ hfe hres hpos; exact bc98_hroute_of_boxAttach μ hfe hres hpos
  · intro μ _ hfe hres; exact bc98_close_a_of_boxAttach μ hfe hres
  · intro μ _ hfe hprob0 hres; exact bc98_bk_from_boxAttach μ hfe hprob0 hres

end StatMech.Walls

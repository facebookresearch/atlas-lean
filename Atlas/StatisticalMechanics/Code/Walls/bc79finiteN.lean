/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Walls.bc78mergedichotomy
import Code.Percolation.BurtonKeaneMerge

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












theorem bc79_enat_012top {k : ℕ∞} (h : 2 ≤ k → k = ⊤) : k = 0 ∨ k = 1 ∨ k = ⊤ := by
  rcases lt_or_ge k 2 with hlt | hge
  · 
    have hle1 : k ≤ 1 := Order.le_of_lt_succ (by exact_mod_cast hlt)
    rcases eq_or_lt_of_le hle1 with heq | hlt1
    · exact Or.inr (Or.inl heq)
    · left
      have : k < 1 := hlt1
      have hle0 : k ≤ 0 := Order.le_of_lt_succ (by simpa using this)
      exact le_antisymm hle0 bot_le
  · exact Or.inr (Or.inr (h hge))




theorem bc79_le_one_of_012top_ne_top {k : ℕ∞} (h : k = 0 ∨ k = 1 ∨ k = ⊤) (hne : k ≠ ⊤) :
    k ≤ 1 := by
  rcases h with h0 | h1 | htop
  · rw [h0]; exact bot_le
  · rw [h1]
  · exact absurd htop hne






theorem bc79_merge_gives_only_012top
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k))
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    k = 0 ∨ k = 1 ∨ k = ⊤ :=
  bc79_enat_012top (fun h2 => burton_keane_merge_excludes_finite_ge_two μ hfe hmergeGeom k hk h2)











theorem bc79_finite_eq_top_compl :
    {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω < ⊤}
      = {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}ᶜ := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, lt_top_iff_ne_top]


theorem bc79_top_measurable :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}
      = numInfiniteClusters d ⁻¹' {⊤} := by ext ω; simp [Set.mem_preimage]
  rw [h]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)





theorem bc79_finite_N_iff_top_null (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] :
    μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔
      μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  rw [bc79_finite_eq_top_compl]
  exact prob_compl_eq_one_iff bc79_top_measurable





theorem bc79_finite_N_iff_le_one (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (htri : k = 0 ∨ k = 1 ∨ k = ⊤) :
    μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  constructor
  · intro hfin
    
    have htopnull : μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
      (bc79_finite_N_iff_top_null μ).mp hfin
    
    have hkne : k ≠ ⊤ := by
      intro hktop
      rw [hktop] at hk; rw [hk] at htopnull; exact one_ne_zero htopnull
    have hkle : k ≤ 1 := bc79_le_one_of_012top_ne_top htri hkne
    have hsub : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k}
        ⊆ {ω | numInfiniteClusters d ω ≤ 1} := by
      intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; rw [hω]; exact hkle
    exact le_antisymm prob_le_one (hk ▸ measure_mono hsub)
  · intro hle1
    
    refine le_antisymm prob_le_one ?_
    refine le_trans (le_of_eq hle1.symm) (measure_mono ?_)
    intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_le_of_lt hω (by decide)







theorem bc79_finite_N_circular
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k))
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω ≤ 1} = 1) := by
  have htri := bc79_merge_gives_only_012top μ hfe hmergeGeom hk
  exact ⟨bc79_finite_N_iff_top_null μ, bc79_finite_N_iff_le_one μ hk htri⟩











theorem bc79_top_subset_atLeastTwo :
    {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤} ⊆ atLeastTwoInfinite d := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [atLeastTwoInfinite, Set.mem_setOf_eq, hω]
  decide






theorem bc79_top_null_of_merge_null (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  measure_mono_null bc79_top_subset_atLeastTwo hmerge






theorem bc79_merge_null_iff (μ : Measure (ConfigSpace (Sym2 (Site d)))) :
    μ (atLeastTwoInfinite d) = 0 ↔
      μ {ω | 2 ≤ numInfiniteClusters d ω ∧ numInfiniteClusters d ω < ⊤} = 0 ∧
      μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  constructor
  · intro hmerge
    refine ⟨measure_mono_null ?_ hmerge, bc79_top_null_of_merge_null μ hmerge⟩
    intro ω hω; simp only [Set.mem_setOf_eq] at hω
    simp only [atLeastTwoInfinite, Set.mem_setOf_eq]; exact hω.1
  · rintro ⟨hfin, htop⟩
    have hdecomp : atLeastTwoInfinite d
        ⊆ {ω : ConfigSpace (Sym2 (Site d)) | 2 ≤ numInfiniteClusters d ω ∧ numInfiniteClusters d ω < ⊤}
          ∪ {ω | numInfiniteClusters d ω = ⊤} := by
      intro ω hω
      simp only [atLeastTwoInfinite, Set.mem_setOf_eq] at hω
      rcases eq_or_lt_of_le (le_top : numInfiniteClusters d ω ≤ ⊤) with heq | hlt
      · exact Or.inr (show numInfiniteClusters d ω = ⊤ from heq)
      · exact Or.inl ⟨hω, hlt⟩
    refine measure_mono_null hdecomp ?_
    exact le_antisymm (le_trans (measure_union_le _ _) (by rw [hfin, htop]; simp)) bot_le

















theorem bc79_directCount_is_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc73_SublatticeForest ω L R) :
    bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R :=
  bc73_covering ω L R h












theorem bc79_directCount_refuted_on_upperLines {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  bc76_buffer_insufficient hL










theorem bc79_directCount_needs_gnCut
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) :=
  fun hforest hexist => bc78_infinitely_many_excluded μ hd L hinv hforest hexist















theorem bc79_residue_noncircular (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
    ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R :=
  bc78_ae_forest_of_dichotomy μ L hinv h0




theorem bc79_bk_from_leaf (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc78_bk_closed μ hd L hinv h0 hexist













theorem bc79_step1_from_leaf (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence μ L)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  
  have htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0 := bc79_bk_from_leaf μ hd L hinv h0 hexist
  
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk hktop
    rw [hktop] at hk; rw [hk] at htop; exact one_ne_zero htop
  
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top hmergeGeom
  
  exact infiniteCluster_unique_ae μ herg hmerge





theorem bc79_top_null_of_forest_and_le_one (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hle1 : μ {ω | numInfiniteClusters d ω ≤ 1} = 1) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc78_top_null_of_le_one μ hle1











theorem bc79_witness_top_branch :
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc78_upperLines_isInfinitelyMany

















theorem bc79_cardinal_verdict
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k))
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    
    ((μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
     (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω ≤ 1} = 1)) ∧
    
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1) := by
  refine ⟨bc79_finite_N_circular μ hfe hmergeGeom hk, ?_⟩
  intro h0 hexist
  exact bc79_step1_from_leaf μ hd L herg hfe hinv h0 hexist hmergeGeom


































theorem bc79_status :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      (μ {ω | numInfiniteClusters 2 ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters 2 ω = ⊤} = 0)) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ →
      (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters 2 ω = k} = 1 →
        ∃ F : Finset (Sym2 (Site 2)), 0 < μ (MergeWitness 2 F k)) →
      ∀ k : ℕ∞, μ {ω | numInfiniteClusters 2 ω = k} = 1 → k = 0 ∨ k = 1 ∨ k = ⊤) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsErgodic (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ →
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 → bc61_CoarseTrifExistence μ L →
      (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters 2 ω = k} = 1 →
        ∃ F : Finset (Sym2 (Site 2)), 0 < μ (MergeWitness 2 F k)) →
      μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1) ∧
    
    (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro μ _; exact bc79_finite_N_iff_top_null μ
  · intro μ _ hfe hmergeGeom k hk; exact bc79_merge_gives_only_012top μ hfe hmergeGeom hk
  · intro μ _ L herg hfe hinv h0 hexist hmergeGeom
    exact bc79_step1_from_leaf μ (by norm_num) L herg hfe hinv h0 hexist hmergeGeom
  · exact bc79_witness_top_branch

end StatMech.Walls

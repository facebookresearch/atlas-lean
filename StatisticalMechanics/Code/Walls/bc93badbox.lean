/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Walls.bc85bootstrap
import Code.Walls.bc81gncutae
import Code.Walls.bc83genuinetrif
import Code.Walls.bc76buffer

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












def bc93_BadBox (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y' : Site d) : Prop :=
  ∃ a b : Site d, a ∈ bc61_boxAround d L y' ∧ b ∈ bc61_boxAround d L y' ∧
    (cluster d ω a).Infinite ∧ (cluster d ω b).Infinite ∧ ¬ Connected d ω a b



theorem bc93_two_infinite_clusters_of_badBox (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y' : Site d}
    (h : bc93_BadBox ω L y') :
    ∃ a b : Site d, (cluster d ω a).Infinite ∧ (cluster d ω b).Infinite ∧
      cluster d ω a ≠ cluster d ω b := by
  obtain ⟨a, b, _, _, hinfa, hinfb, hncon⟩ := h
  refine ⟨a, b, hinfa, hinfb, ?_⟩
  intro heq
  
  apply hncon
  have : b ∈ cluster d ω a := by rw [heq]; exact self_mem_cluster ω b
  rw [mem_cluster] at this; exact this
















theorem bc93_no_badBox_of_le_one (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (hN : numInfiniteClusters d ω ≤ 1) (y' : Site d) :
    ¬ bc93_BadBox ω L y' := by
  rintro ⟨a, b, _, _, hinfa, hinfb, hncon⟩
  exact hncon (bc81_infinite_clusters_coincide_of_le_one ω hN hinfa hinfb)



theorem bc93_badBox_free_of_le_one (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (hN : numInfiniteClusters d ω ≤ 1) :
    ∀ y' : Site d, ¬ bc93_BadBox ω L y' :=
  fun y' => bc93_no_badBox_of_le_one ω L hN y'












theorem bc93_two_le_numInfinite_of_badBox (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y' : Site d}
    (h : bc93_BadBox ω L y') :
    2 ≤ numInfiniteClusters d ω := by
  obtain ⟨a, b, hinfa, hinfb, hne⟩ := bc93_two_infinite_clusters_of_badBox ω L h
  
  have hmemA : cluster d ω a ∈ infiniteClusters d ω := ⟨hinfa, a, rfl⟩
  have hmemB : cluster d ω b ∈ infiniteClusters d ω := ⟨hinfb, b, rfl⟩
  have hnt : (infiniteClusters d ω).Nontrivial := ⟨_, hmemA, _, hmemB, hne⟩
  change (2 : ℕ∞) ≤ (infiniteClusters d ω).encard
  rw [show (2 : ℕ∞) = 1 + 1 from rfl]
  exact Order.add_one_le_of_lt (Set.one_lt_encard_iff_nontrivial.mpr hnt)




theorem bc93_not_le_one_of_badBox (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y' : Site d}
    (h : bc93_BadBox ω L y') :
    ¬ numInfiniteClusters d ω ≤ 1 := by
  intro hle
  have := bc93_two_le_numInfinite_of_badBox ω L h
  
  exact absurd (le_trans this hle) (by decide)












theorem bc93_upperLines_witnesses_in_box {L : ℕ} (hL : 3 ≤ L) :
    bc57_pt (3 * (L : ℤ) + 1) 1 ∈ bc61_boxAround 2 L (bc76_yBuf L) ∧
    bc57_pt (3 * (L : ℤ) + 1) 3 ∈ bc61_boxAround 2 L (bc76_yBuf L) := by
  refine ⟨bc76_boxBuf_boundary_mem ?_, bc76_boxBuf_boundary_mem ?_⟩
  · simp only [Int.natAbs_one]; omega
  · rw [show (3 : ℤ).natAbs = 3 from rfl]; omega














theorem bc93_singleBox_trif_perConfig (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    bc83_genuineTrif ω L y ↔ bc61_IsCoarseTrifurcation ω L y :=
  bc83_genuineTrif_iff_coarse ω L y





theorem bc93_le_one_subset_no_badBox (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (hN : numInfiniteClusters d ω ≤ 1) :
    ∀ y' : Site d, ¬ bc93_BadBox ω L y' :=
  bc93_badBox_free_of_le_one ω L hN






theorem bc93_no_badBox_ae_of_uniqueness (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (L : ℕ) (h1 : μ {ω | numInfiniteClusters d ω ≤ 1} = 1) (y' : Site d) :
    ∀ᵐ ω ∂μ, ¬ bc93_BadBox ω L y' := by
  have hsub : {ω | numInfiniteClusters d ω ≤ 1} ⊆ {ω | ¬ bc93_BadBox ω L y'} := by
    intro ω hω
    exact bc93_no_badBox_of_le_one ω L hω y'
  rw [ae_iff]
  have : μ {ω | ¬ ¬ bc93_BadBox ω L y'} ≤ μ {ω | ¬ numInfiniteClusters d ω ≤ 1} := by
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq, not_not] at hω ⊢
    exact bc93_not_le_one_of_badBox ω L hω
  
  have hms : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω ≤ 1} :=
    measurable_numInfiniteClusters (MeasurableSet.of_discrete)
  have hzero : μ {ω | ¬ numInfiniteClusters d ω ≤ 1} = 0 := by
    have heq : {ω : ConfigSpace (Sym2 (Site d)) | ¬ numInfiniteClusters d ω ≤ 1}
        = {ω | numInfiniteClusters d ω ≤ 1}ᶜ := rfl
    rw [heq, prob_compl_eq_zero_iff hms]
    exact h1
  exact le_antisymm (le_trans this (le_of_eq hzero)) (zero_le')













theorem bc93_bk_from_no_badBox_effect (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc85_dc_bootstrap μ hd L hinv hforest_ae hexist















theorem bc93_upperLines_singleBox_trif {L : ℕ} (hL : 3 ≤ L) :
    bc83_genuineTrif bc60_upperLines L (0 : Site 2) :=
  (bc93_singleBox_trif_perConfig bc60_upperLines L 0).mpr (bc80_upperLines_ambient_coarseTrif hL)






theorem bc93_upperLines_multiBox_fails_and_N_top {L : ℕ} (hL : 3 ≤ L) :
    (bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
     Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
     ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
        ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
        ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) ∧
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  ⟨bc76_buffer_insufficient hL, bc85_upperLines_N_top⟩








































theorem bc93_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2),
      bc83_genuineTrif ω L y ↔ bc61_IsCoarseTrifurcation ω L y) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), numInfiniteClusters 2 ω ≤ 1 →
      ∀ y' : Site 2, ¬ bc93_BadBox ω L y') ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y' : Site 2), bc93_BadBox ω L y' →
      2 ≤ numInfiniteClusters 2 ω) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), numInfiniteClusters 2 ω ≤ 1 →
      ∀ y' : Site 2, ¬ bc93_BadBox ω L y') ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ) (y' : Site 2),
      μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1 → ∀ᵐ ω ∂μ, ¬ bc93_BadBox ω L y') ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω L y; exact bc93_singleBox_trif_perConfig ω L y
  · intro ω L hN y'; exact bc93_no_badBox_of_le_one ω L hN y'
  · intro ω L y' h; exact bc93_two_le_numInfinite_of_badBox ω L h
  · intro ω L hN y'; exact bc93_le_one_subset_no_badBox ω L hN y'
  · intro μ _ L y' h1; exact bc93_no_badBox_ae_of_uniqueness μ L h1 y'
  · intro μ _ L hinv hforest_ae hexist
    exact bc93_bk_from_no_badBox_effect μ (by norm_num) L hinv hforest_ae hexist
  · exact bc85_upperLines_N_top

end StatMech.Walls

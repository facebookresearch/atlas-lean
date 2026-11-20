/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































































import Mathlib
import Code.Walls.bc84leafboundary
import Code.Walls.bc83genuinetrif
import Code.Walls.bc82singleboxcount
import Code.Walls.bc79finiteN

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












theorem bc85_expectation_identity (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (L R : ℕ) :
    ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
      = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ :=
  bc62_coarse_expectation μ hinv L R


















theorem bc85_prob_zero_of_count_forest (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
  bc77_coarseTrif_prob_eq_zero_ae μ L
    (fun R => (2 * L + 1) ^ d * boxSV_boundaryCard d R)
    (fun R => bc85_expectation_identity μ hinv L R)
    (bc77_ae_bound_of_ae_forest μ L hforest_ae)
    (fun R => bkc_boxFinsetBK_card_pos d R)
    (bc73_const_boundary_vol_tendsto d hd L)













theorem bc85_exclude_infinite_N (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  by_contra htop
  have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr htop
  have := hexist hpos
  rw [h0] at this
  exact lt_irrefl 0 this




















theorem bc85_dc_bootstrap (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc85_exclude_infinite_N μ L (bc85_prob_zero_of_count_forest μ hd L hinv hforest_ae) hexist







theorem bc85_dc_bootstrap_of_leaf (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc85_exclude_infinite_N μ L h0 hexist





















theorem bc85_dc_step1_uniqueness (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  
  have htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
    bc85_dc_bootstrap μ hd L hinv hforest_ae hexist
  
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk hktop
    rw [hktop] at hk; rw [hk] at htop; exact one_ne_zero htop
  
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top hmergeGeom
  
  exact infiniteCluster_unique_ae μ herg hmerge















theorem bc85_finiteN_iff_top_null (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] :
    μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc79_finite_N_iff_top_null μ











theorem bc85_count_on_finiteN_needs_le_one (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (hN : numInfiniteClusters d ω ≤ 1) (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃ ∧
      (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) :=
  bc81_coarseTrif_arms_connected_of_le_one ω L hN h











theorem bc85_finiteN_not_enough_note {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  bc76_buffer_insufficient hL









theorem bc85_bootstrap_noncircular_order (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) →
      ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ∧
    
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨fun h0 => bc78_ae_forest_of_dichotomy μ L hinv h0, ?_⟩
  intro h0 hexist
  exact bc85_exclude_infinite_N μ L h0 hexist







theorem bc85_upperLines_N_top :
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc60_numInfiniteClusters_top





theorem bc85_upperLines_null_of_bootstrap
    (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (htop : μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) :
    μ {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 := by
  refine measure_mono_null ?_ htop
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [hω]; exact bc60_numInfiniteClusters_top























theorem bc85_circularity_verdict (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    
    ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) →
      ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ∧
    
    (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨fun hforest_ae hexist => bc85_dc_bootstrap μ hd L hinv hforest_ae hexist, ?_, ?_⟩
  · intro h0; exact bc78_ae_forest_of_dichotomy μ L hinv h0
  · exact bc85_finiteN_iff_top_null μ


































theorem bc85_status :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsErgodic (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ →
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) →
      bc61_CoarseTrifExistence μ L →
      (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters 2 ω = k} = 1 →
        ∃ F : Finset (Sym2 (Site 2)), 0 < μ (MergeWitness 2 F k)) →
      μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      (μ {ω | numInfiniteClusters 2 ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters 2 ω = ⊤} = 0)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), numInfiniteClusters 2 ω ≤ 1 →
      bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site 2, Connected 2 ω a₁ a₂ ∧ Connected 2 ω a₁ a₃ ∧ Connected 2 ω a₂ a₃) ∧
    
    (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro μ _ L hinv hforest_ae hexist
    exact bc85_dc_bootstrap μ (by norm_num) L hinv hforest_ae hexist
  · intro μ _ L herg hfe hinv hforest_ae hexist hmergeGeom
    exact bc85_dc_step1_uniqueness μ (by norm_num) L herg hfe hinv hforest_ae hexist hmergeGeom
  · intro μ _; exact bc85_finiteN_iff_top_null μ
  · intro ω L y hN h
    obtain ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃, _⟩ := bc85_count_on_finiteN_needs_le_one ω L hN h
    exact ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃⟩
  · exact bc85_upperLines_N_top

end StatMech.Walls

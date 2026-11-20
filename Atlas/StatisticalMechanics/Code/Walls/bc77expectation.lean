/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Mathlib
import Code.Walls.bc76buffer
import Code.Walls.bc73sublattice
import Code.Walls.bc62coarseclose

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













theorem bc77_expected_count (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (L R : ℕ) :
    ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
      = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ :=
  bc62_coarse_expectation μ hinv L R





















theorem bc77_coarseTrif_prob_eq_zero_ae (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hbound_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | bc61_IsCoarseTrifurcation ω L 0} with hp
  have hkey : ∀ R, ((boxFinsetBK d R).card : ℝ≥0∞) * p ≤ (bdry R : ℝ≥0∞) := by
    intro R
    have hle : ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞) := by
      calc ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (bdry R : ℝ≥0∞) ∂μ := by
            
            refine lintegral_mono_ae ?_
            filter_upwards [hbound_ae R] with ω hω
            exact_mod_cast hω
        _ = (bdry R : ℝ≥0∞) := by rw [lintegral_const]; simp
    rw [hexp R]; exact hle
  have hpfin : p ≠ ⊤ := by rw [hp]; exact (measure_ne_top μ _)
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ R, ((boxFinsetBK d R).card : ℝ) * pr ≤ (bdry R : ℝ) := by
    intro R
    have h := hkey R
    have h' : (((boxFinsetBK d R).card : ℝ≥0∞) * p).toReal ≤ (bdry R : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ R, (0 : ℝ) < ((boxFinsetBK d R).card : ℝ) := fun R => by exact_mod_cast hvol R
  have hle : ∀ R, pr ≤ (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ) := by
    intro R
    rw [le_div_iff₀ (hvolr R)]
    linarith [hkeyr R]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this












theorem bc77_top_null_of_ae_bound (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hbound_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  have hprob0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
    bc77_coarseTrif_prob_eq_zero_ae μ L bdry hexp hbound_ae hvol hdens
  by_contra htop
  have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr htop
  have := hexist hpos
  rw [hprob0] at this
  exact lt_irrefl 0 this












theorem bc77_ae_bound_of_ae_forest (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) :
    ∀ R : ℕ, ∀ᵐ ω ∂μ,
      bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
  intro R
  filter_upwards [hforest_ae R] with ω hω
  exact bc73_covering ω L R hω












theorem bc77_top_null_of_ae_forest (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc77_top_null_of_ae_bound μ L
    (fun R => (2 * L + 1) ^ d * boxSV_boundaryCard d R)
    (fun R => bc77_expected_count μ hinv L R)
    (bc77_ae_bound_of_ae_forest μ L hforest_ae)
    (fun R => bkc_boxFinsetBK_card_pos d R)
    (bc73_const_boundary_vol_tendsto d hd L)
    hexist










theorem bc77_ae_forest_iff_bad_null (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L R : ℕ)
    (hmeas : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R}) :
    (∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ↔
      μ {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R} = 0 := by
  constructor
  · intro hae
    rw [MeasureTheory.ae_iff] at hae
    simpa using hae
  · intro hnull
    rw [MeasureTheory.ae_iff]
    simpa using hnull






theorem bc77_top_null_of_bad_null (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hmeasbad : ∀ R : ℕ, MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R})
    (hbadnull : ∀ R : ℕ, μ {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R} = 0)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc77_top_null_of_ae_forest μ hd L hinv
    (fun R => (bc77_ae_forest_iff_bad_null μ L R (hmeasbad R)).mpr (hbadnull R))
    hexist














theorem bc77_upperLines_singleton :
    ({bc60_upperLines} : Set (ConfigSpace (Sym2 (Site 2)))) = {ω | ω = bc60_upperLines} := by
  ext ω; simp [Set.mem_singleton_iff]





theorem bc77_upperLines_null_of_singleton_null
    (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (h0 : μ {bc60_upperLines} = 0) :
    μ {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 := by
  rwa [← bc77_upperLines_singleton]











































theorem bc77_circularity_note
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    
    ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    (∀ R : ℕ, MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R} →
      ((∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ↔
        μ {ω : ConfigSpace (Sym2 (Site d)) | ¬ bc73_SublatticeForest ω L R} = 0)) := by
  refine ⟨fun hforest_ae hexist => bc77_top_null_of_ae_forest μ hd L hinv hforest_ae hexist, ?_⟩
  intro R hmeas
  exact bc77_ae_forest_iff_bad_null μ L R hmeas





























theorem bc77_status :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
        (L : ℕ) (bdry : ℕ → ℕ),
      (∀ R : ℕ, ((boxFinsetBK 2 R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
          = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ bdry R) →
      (∀ R, 0 < (boxFinsetBK 2 R).card) →
      Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (({bc60_upperLines} : Set (ConfigSpace (Sym2 (Site 2)))) = {ω | ω = bc60_upperLines}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ _ L bdry hexp hbound_ae hvol hdens hexist
    exact bc77_top_null_of_ae_bound μ L bdry hexp hbound_ae hvol hdens hexist
  · intro μ _ L hinv hforest_ae hexist
    exact bc77_top_null_of_ae_forest μ (by norm_num) L hinv hforest_ae hexist
  · exact bc77_upperLines_singleton

end StatMech.Walls

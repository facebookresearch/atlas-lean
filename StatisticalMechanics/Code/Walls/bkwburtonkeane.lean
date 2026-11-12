/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Walls.bkmmerge
import Code.Walls.bc120closure
import Code.Walls.bc69count
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


















theorem bkw_lemma26_insertion_tolerance_pp
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ L : ℕ, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} :=
  bkm_coarseTrifExistence_diag μ hinv hfe htop


















theorem bkw_count_half_of_forest
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
    μ {ω | numInfiniteClusters 2 ω = ⊤} = 0 := by
  by_contra hne
  have htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤} := pos_iff_ne_zero.mpr hne
  
  obtain ⟨L, hpos⟩ := bkw_lemma26_insertion_tolerance_pp μ hinv hfe htop
  have hexist : bc61_CoarseTrifExistence μ L := fun _ => hpos
  
  have hzero : μ {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
    bc61_infiniteClusters_top_null_of_coarse μ L (fun R => boxSV_boundaryCard 2 R)
      (fun R => bc62_coarse_expectation μ hinv L R)
      (fun ω R => bc69_coarseTcount_le_boundary ω L R (hforest ω L R))
      (fun R => bkc_boxFinsetBK_card_pos 2 R)
      (bkc_boundary_vol_tendsto 2 (by norm_num))
      hexist
  exact hne hzero















theorem bkw_bk_uniqueness_of_forest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 with hμ
  have herg : IsErgodic (G := Multiplicative (Site 2)) μ :=
    bkc_bernoulli_isErgodic (by norm_num) p hp1
  have hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ := herg.isTranslationInvariant
  have hfe : HasFiniteEnergyMerge μ := bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0
  have htop : μ {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
    bkw_count_half_of_forest μ hinv hfe hforest
  exact bc120_uniqueness_of_top_null μ herg hfe htop





theorem bkw_top_null_of_forest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω | numInfiniteClusters 2 ω = ⊤} = 0 := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 with hμ
  have hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ :=
    (bkc_bernoulli_isErgodic (by norm_num) p hp1).isTranslationInvariant
  have hfe : HasFiniteEnergyMerge μ := bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0
  exact bkw_count_half_of_forest μ hinv hfe hforest


































theorem bkw_status (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ →
      0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
      ∃ L : ℕ, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    ((∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ _ hinv hfe htop; exact bkw_lemma26_insertion_tolerance_pp μ hinv hfe htop
  · intro μ _ hinv hfe hforest; exact bkw_count_half_of_forest μ hinv hfe hforest
  · intro hforest; exact (bkw_bk_uniqueness_of_forest p hp1 hp0 hforest).2.1

end StatMech.Walls

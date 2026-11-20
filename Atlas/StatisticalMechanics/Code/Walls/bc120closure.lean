/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































































import Mathlib
import Code.Walls.bc109finiteenergy
import Code.Walls.bc112sepcontract
import Code.Walls.bc116armproof

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












theorem bc120_kne_top_of_top_null (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0) :
    ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
  intro k hk hktop
  
  subst hktop
  rw [hk] at htop
  exact one_ne_zero htop












theorem bc120_merge_null_of_top_null (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0) :
    μ (atLeastTwoInfinite d) = 0 :=
  merge_event_null μ herg hfe (bc120_kne_top_of_top_null μ htop)
    (fun k hk2 hktop hk => hmergeGeom_discharged μ k hk2 hktop hk)














theorem bc120_uniqueness_of_top_null (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  have hmerge : μ (atLeastTwoInfinite d) = 0 := bc120_merge_null_of_top_null μ herg hfe htop
  exact ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩






















theorem bc120_bk_uniqueness_of_residues (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  have herg : IsErgodic (G := Multiplicative (Site d)) μ := bkc_bernoulli_isErgodic hd p hp1
  have hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ := herg.isTranslationInvariant
  have hfe : HasFiniteEnergyMerge μ := bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0
  
  have htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
    bc109_bk_count_half_pp hd p hp1 hp0 hinv L hGlobal hcoarseRoute
  
  exact bc120_uniqueness_of_top_null μ herg hfe htop




theorem bc120_top_null_of_residues (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc109_bk_count_half_pp hd p hp1 hp0
    (bkc_bernoulli_isErgodic hd p hp1).isTranslationInvariant L hGlobal hcoarseRoute














theorem bc120_bk_uniqueness_via_bc73 (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) *
          bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) L) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  have herg : IsErgodic (G := Multiplicative (Site d)) μ := bkc_bernoulli_isErgodic hd p hp1
  have hfe : HasFiniteEnergyMerge μ := bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0
  have htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
    bc73_infiniteClusters_top_null μ hd L hexp hforest hexist
  exact bc120_uniqueness_of_top_null μ herg hfe htop




theorem bc120_bc73_of_bc69 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) : bc73_SublatticeForest ω L R :=
  bc108_sublatticeForest_of_globalForest ω L R h













theorem bc120_gap1_discharged (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hL : 3 ≤ L) :
    bc112_SeparatedArmGraph ω L R :=
  bc112_separatedArmGraph_holds hd ω L R hL







theorem bc120_armCovered_of_H1 (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {B H : Site d → Prop} (hmem : bc116_ArmPathMembership ω L y B H) :
    bc114_ArmCovered (bc67_contractedLattice ω L y) B H :=
  bc116_armCovered_concrete_of_membership ω L y hmem






theorem bc120_full_separated_iff_gap2 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R :=
  bc112_boundaryLeafResidue_iff_full ω L R











































theorem bc120_status (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ],
      IsErgodic (G := Multiplicative (Site d)) μ → HasFiniteEnergyMerge μ →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0 →
      (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
        ∧ μ (atLeastTwoInfinite d) = 0
        ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧
    
    (∀ (L : ℕ) (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R),
      (0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) →
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L → bc112_SeparatedArmGraph ω L R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ _ herg hfe htop; exact bc120_uniqueness_of_top_null μ herg hfe htop
  · intro L hGlobal hcoarseRoute
    exact (bc120_bk_uniqueness_of_residues hd p hp1 hp0 L hGlobal hcoarseRoute).2.1
  · intro ω L R hL; exact bc120_gap1_discharged hd ω L R hL

end StatMech.Walls

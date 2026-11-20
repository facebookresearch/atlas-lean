/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Walls.bc107harmbox
import Code.Walls.bc70globalforest
import Code.Percolation.BurtonKeaneClose

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














theorem bc109_precursor_pp (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | bc61_IsCoarseTrifurcation ω L 0} :=
  bc107_coarseRoute_precursor_genuine
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) L a₁ a₂ a₃ b₁ b₂ b₃ hpos












theorem bc109_coarseTrifExistence_pp (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) L :=
  bc62_coarseTrifExistence_of_route
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) L hcoarseRoute
















theorem bc109_bk_count_half_pp (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d))
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc107_bk_residue_after_harmbox_discharge
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) hd hinv
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) L hGlobal hcoarseRoute














theorem bc109_precursor_witness_upperLines {L : ℕ} (hL : 3 ≤ L) :
    bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L
      (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3)
      (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3) :=
  bc62_upperLines_mem_coarsePrecursor hL






theorem bc109_precursor_forced_coarseTrif_upperLines {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation
      (forceOpenFinset {s(bc57_pt (L : ℤ) 1, bc57_pt ((L : ℤ) + 1) 1),
        s(bc57_pt (L : ℤ) 2, bc57_pt ((L : ℤ) + 1) 2),
        s(bc57_pt (L : ℤ) 3, bc57_pt ((L : ℤ) + 1) 3)} bc60_upperLines) L 0 :=
  bc62_upperLines_forced_coarseTrif hL






















theorem bc109_status (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    
    (∀ (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) →
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧
    
    (∀ (L : ℕ),
      (0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) →
      bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) L) ∧
    
    (∀ (hinv : IsTranslationInvariant (G := Multiplicative (Site d))
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)) (L : ℕ),
      (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R) →
      (0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) →
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L a₁ a₂ a₃ b₁ b₂ b₃ hpos
    exact bc109_precursor_pp p hp1 hp0 L a₁ a₂ a₃ b₁ b₂ b₃ hpos
  · intro L hcoarseRoute
    exact bc109_coarseTrifExistence_pp p hp1 hp0 L hcoarseRoute
  · intro hinv L hGlobal hcoarseRoute
    exact bc109_bk_count_half_pp hd p hp1 hp0 hinv L hGlobal hcoarseRoute

end StatMech.Walls

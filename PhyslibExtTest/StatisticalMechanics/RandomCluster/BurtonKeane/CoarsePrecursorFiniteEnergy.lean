/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarsePrecursorFiniteEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarsePrecursorFiniteEnergy`

For Bernoulli(1/2) bond percolation on the plane:
* `bc109_precursor_pp`: a positive-probability coarse precursor gives coarse trifurcations of
  positive probability;
* `bc109_coarseTrifExistence_pp` from the coarse route;
* `bc109_bk_count_half_pp` applied with the Bernoulli translation invariance.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarsePrecursorFiniteEnergy

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The Bernoulli(1/2) bond percolation measure on the planar lattice. -/
noncomputable abbrev bern2 : Measure (ConfigSpace (Sym2 (Site 2))) :=
  bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)

/-- `bern2` has finite energy. -/
theorem bern2_fe : HasFiniteEnergyMerge bern2 :=
  bkc_bernoulli_hasFiniteEnergyMerge _ _ (by norm_num)

/-- `bern2` is translation invariant. -/
theorem bern2_inv : IsTranslationInvariant (G := Multiplicative (Site 2)) bern2 :=
  (bkc_bernoulli_isErgodic (d := 2) (by norm_num) _ _).isTranslationInvariant

-- A positive-probability precursor gives positive-probability coarse trifurcations.
example (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2)
    (hpos : 0 < bern2 (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) :
    0 < bern2 {ω | bc61_IsCoarseTrifurcation ω L 0} :=
  bc109_precursor_pp _ _ (by norm_num) L _ _ _ _ _ _ hpos

-- The coarse route gives the coarse step.
example (L : ℕ) (hroute : 0 < bern2 {ω | numInfiniteClusters 2 ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site 2, 0 < bern2 (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bc61_CoarseTrifExistence bern2 L :=
  bc109_coarseTrifExistence_pp _ _ (by norm_num) L hroute

-- The global forest and the coarse route give `N < ⊤` almost surely.
example (L : ℕ) (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hroute : 0 < bern2 {ω | numInfiniteClusters 2 ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site 2, 0 < bern2 (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bern2 {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bc109_bk_count_half_pp (by norm_num) _ _ (by norm_num) bern2_inv L hGlobal hroute

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarsePrecursorFiniteEnergy

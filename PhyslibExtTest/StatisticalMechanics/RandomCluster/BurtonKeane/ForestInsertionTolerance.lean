/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestInsertionTolerance

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestInsertionTolerance`

For Bernoulli(1/2) bond percolation on the plane, in conditional form (assuming a global contracted
forest for every configuration):
* `bkw_top_null_of_forest`: `N = ⊤` is null;
* `bkw_bk_uniqueness_of_forest`: at most one infinite cluster almost surely;
* `bkw_status`: its first clause (a coarse trifurcation at some scale from `N = ⊤`) for a general
  invariant finite-energy measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestInsertionTolerance

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- A global forest makes `N = ⊤` null for Bernoulli(1/2).
example (hforest : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)
      {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bkw_top_null_of_forest _ _ (by norm_num) hforest

-- And gives at most one infinite cluster.
example (hforest : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)
      {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  (bkw_bk_uniqueness_of_forest _ _ (by norm_num) hforest).2.2

-- `N = ⊤` with positive probability gives coarse trifurcations at some scale.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
    (hfe : HasFiniteEnergyMerge μ) (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ L : ℕ, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} :=
  (bkw_status (1 / 2) (by norm_num) (by norm_num)).1 μ hinv hfe htop

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestInsertionTolerance

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane`

* `measure_encounter_eq_zero`, which this module uses, for Bernoulli(1/2) bond percolation on
  `ℤ²` (translation invariance from `bernoulli_lattice_ergodic`);
* `cbk_canonical_uniqueness` for Bernoulli(1/2) in conditional form (only the trifurcation
  hypothesis assumed).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation
open scoped NNReal
open _root_.MathlibExt.Probability.Percolation.BurtonKeaneWanted
  (IsEncounterPoint measure_encounter_eq_zero bernoulli_lattice_ergodic
    bernoulli_finiteEnergyMerge)

-- Encounter points have probability zero under Bernoulli(1/2) on `ℤ²`.
example : bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2 : ℝ≥0) (by norm_num)
    {ω | IsEncounterPoint 2 ω 0} = 0 :=
  measure_encounter_eq_zero _ (by norm_num)
    (bernoulli_lattice_ergodic (by norm_num) (1 / 2 : ℝ≥0) (by norm_num)).1

-- Uniqueness for Bernoulli(1/2) from the encounter-point hypothesis.
example (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2 : ℝ≥0) (by norm_num)
      {ω | numInfiniteClusters 2 ω = ⊤} →
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2 : ℝ≥0) (by norm_num)
      {ω | IsEncounterPoint 2 ω 0}) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2 : ℝ≥0) (by norm_num)
      (atLeastTwoInfinite 2) = 0 :=
  (cbk_canonical_uniqueness _ (by norm_num)
    (bernoulli_lattice_ergodic (by norm_num) (1 / 2 : ℝ≥0) (by norm_num))
    (bernoulli_finiteEnergyMerge _ (by norm_num) (by norm_num)) htrif).2.1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane

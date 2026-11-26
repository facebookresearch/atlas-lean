/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestFiniteEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestFiniteEnergy`

In the plane:
* `bfe_perConfig_count` for the upper-lines configuration at `R = 3`;
* `bfe_boxCard`: the radius-one box has `9` sites;
* `bfe_dichotomy` for Bernoulli(1/2) bond percolation;
* `bfe_bk_atLeastTwo` applied to Bernoulli(1/2) under the scale-zero step.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestFiniteEnergy

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

-- The scale-zero coarse count of the upper lines is bounded by the next boundary.
example : bc61_coarseTcount bc60_upperLines 0 3 ≤ boxSV_boundaryCard 2 (3 + 1) :=
  bfe_perConfig_count bc60_upperLines 3

-- The radius-one planar box has nine sites.
example : ((boxFinsetBK 2 1).card : ℝ) = 9 := by
  rw [bfe_boxCard]; norm_num

-- Scale-zero coarse trifurcations at the origin have probability zero under Bernoulli(1/2).
example : bern2 {ω | bc61_IsCoarseTrifurcation ω 0 0} = 0 :=
  bfe_dichotomy (by norm_num) bern2 bern2_inv

-- Under the scale-zero step, Bernoulli(1/2) has no two infinite clusters.
example (hexist : bc61_CoarseTrifExistence bern2 0) : bern2 (atLeastTwoInfinite 2) = 0 :=
  bfe_bk_atLeastTwo (by norm_num) _ _ (by norm_num) hexist

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestFiniteEnergy

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeDichotomy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeDichotomy`

In the plane:
* `bc78_upperLines_coarseTrif`: the upper lines are a coarse trifurcation with `N = ⊤` at `L = 3`;
* `bc78_status`: the upper lines have infinitely many infinite clusters;
* `bc78_bk_closed` and `bc78_upperLines_excluded_null` applied to Bernoulli(1/2).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeDichotomy

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

-- At `L = 3` the upper lines are a coarse trifurcation with infinitely many infinite clusters.
example : bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) ∧
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc78_upperLines_coarseTrif le_rfl

-- The upper lines have `N = ⊤`.
example : numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc78_status.2.2

-- The closed dichotomy applied to Bernoulli(1/2).
example (L : ℕ) (h0 : bern2 {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence bern2 L) :
    bern2 {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bc78_bk_closed bern2 (by norm_num) L bern2_inv h0 hexist

-- If `N = ⊤` is null, so is the upper-lines configuration.
example (htop : bern2 {ω | numInfiniteClusters 2 ω = ⊤} = 0) :
    bern2 {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 :=
  bc78_upperLines_excluded_null bern2 htop

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeDichotomy

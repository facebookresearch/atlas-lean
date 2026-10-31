/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifMerge

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifMerge`

In the plane:
* `bkm_recenterBoxMerge_diag` and `bkm_recenterBoxMerge_of_le` at explicit scales;
* `bkm_box_subset_boxAround` at the origin;
* `bkm_coarseTrifExistence_atSomeScale` and `bkm_status` applied to Bernoulli(1/2).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifMerge

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

-- The recentred box merge on the diagonal and below it.
example : bc119_RecenterBoxMerge 2 3 3 ∧ bc119_RecenterBoxMerge 2 5 2 :=
  ⟨bkm_recenterBoxMerge_diag 3, bkm_recenterBoxMerge_of_le (by norm_num)⟩

-- The origin of the radius-one box lies in the radius-3 box at the origin.
example : (0 : Site 2) ∈ bc61_boxAround 2 3 0 :=
  bkm_box_subset_boxAround (n := 1) (by norm_num) (by simp [box])

-- If Bernoulli(1/2) had `N = ⊤` with positive probability, the coarse step holds at some scale.
example (htop : 0 < bern2 {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ L : ℕ, bc61_CoarseTrifExistence bern2 L :=
  bkm_coarseTrifExistence_atSomeScale bern2 bern2_inv bern2_fe htop

-- The same through `bkm_status`.
example (htop : 0 < bern2 {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ L : ℕ, bc61_CoarseTrifExistence bern2 L :=
  bkm_status.2.2 bern2 bern2_inv bern2_fe htop

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifMerge

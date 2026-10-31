/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeSeverance

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeSeverance`

In the plane:
* `bc115_merge_upperLines_emptyWiring` at `L = 3`;
* `bc115_coarsePrecursor_of_coarseTrif` and `bc115_coarseTrif_disconnection_free` applied to the
  upper-lines coarse trifurcation;
* `bc115_coarseTrifExistence_of_merge` applied to Bernoulli(1/2) bond percolation.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeSeverance

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

-- Some wiring of the upper lines is a coarse trifurcation at `L = 3`.
example : ∃ W : Finset (Sym2 (Site 2)),
    bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) 3 0 :=
  bc115_merge_upperLines_emptyWiring le_rfl

-- The upper lines lie in a coarse precursor.
example : ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site 2,
    bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 3 a₁ a₂ a₃ b₁ b₂ b₃ :=
  bc115_coarsePrecursor_of_coarseTrif 3 (bc61_wholeBox_severs_upperLines le_rfl)

-- Three pairwise disconnected sites outside the box for the upper lines.
example : ∃ a₁ a₂ a₃ : Site 2,
    ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁ a₂ ∧
    ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁ a₃ ∧
    ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₂ a₃ :=
  bc115_coarseTrif_disconnection_free 3 (bc61_wholeBox_severs_upperLines le_rfl)

-- The merge at every scale gives the coarse step for Bernoulli(1/2).
example (L : ℕ) (hmerge : ∀ n : ℕ, bc115_CoarseTrifMerge 2 L n) :
    bc61_CoarseTrifExistence bern2 L :=
  bc115_coarseTrifExistence_of_merge bern2 bern2_fe L hmerge

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeSeverance

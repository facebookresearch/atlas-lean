/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRemoveSites

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRemoveSites`

In the plane:
* `bc62_upperLines_forced_coarseTrif`: forcing three box edges makes the upper lines a coarse
  trifurcation at `L = 3`;
* `bc62_boxVertex_mem` at an explicit vertex;
* `bc62_coarse_expectation` and `bc62_coarseTrifProb_const` for Bernoulli(1/2);
* `bc62_measurableSet_coarseTrif` at an explicit centre.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRemoveSites

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

-- Forcing the three arm edges of the upper lines gives a coarse trifurcation at `L = 3`.
example : bc61_IsCoarseTrifurcation
    (forceOpenFinset {s(bc57_pt ((3 : ℕ) : ℤ) 1, bc57_pt (((3 : ℕ) : ℤ) + 1) 1),
      s(bc57_pt ((3 : ℕ) : ℤ) 2, bc57_pt (((3 : ℕ) : ℤ) + 1) 2),
      s(bc57_pt ((3 : ℕ) : ℤ) 3, bc57_pt (((3 : ℕ) : ℤ) + 1) 3)} bc60_upperLines) 3 0 :=
  bc62_upperLines_forced_coarseTrif le_rfl

-- The vertex `(3, 2)` lies in the radius-3 box.
example : bc57_pt ((3 : ℕ) : ℤ) 2 ∈ bc61_boxAround 2 3 0 :=
  bc62_boxVertex_mem (by norm_num) (by norm_num)

-- The expected coarse count under Bernoulli(1/2).
example (L R : ℕ) :
    ((boxFinsetBK 2 R).card : ENNReal) * bern2 {ω | bc61_IsCoarseTrifurcation ω L 0}
      = ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂bern2 :=
  bc62_coarse_expectation bern2 bern2_inv L R

-- The coarse-trifurcation probability does not depend on the centre.
example (L : ℕ) : bern2 {ω | bc61_IsCoarseTrifurcation ω L (bc57_pt 5 7)}
    = bern2 {ω | bc61_IsCoarseTrifurcation ω L 0} :=
  bc62_coarseTrifProb_const bern2 bern2_inv L _

-- Coarse trifurcation events are measurable.
example : MeasurableSet {ω : ConfigSpace (Sym2 (Site 2)) |
    bc61_IsCoarseTrifurcation ω 3 (bc57_pt 1 1)} :=
  bc62_measurableSet_coarseTrif 3 _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRemoveSites

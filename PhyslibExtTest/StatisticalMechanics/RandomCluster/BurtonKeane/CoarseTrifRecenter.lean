/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRecenter

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRecenter`

In the plane:
* `bc119_recenter_upperLines_witness` at `L = 3`;
* `bc119_commonBox_of_close` for three coinciding sites at scale `0`;
* `bc119_originCoarseTrif_of_yCoarseTrif` and `bc119_coarseTrifExistence_of_recenterResidue`
  applied to Bernoulli(1/2) bond percolation.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRecenter

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

-- Some wiring of the upper lines has a coarse trifurcation at some centre for `L = 3`.
example : ∃ (y : Site 2) (W : Finset (Sym2 (Site 2))),
    bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) 3 y :=
  bc119_recenter_upperLines_witness le_rfl

-- Three equal sites lie in the scale-zero box around the first one.
example (x : Site 2) : x ∈ bc61_boxAround 2 0 x ∧ x ∈ bc61_boxAround 2 0 x ∧
    x ∈ bc61_boxAround 2 0 x :=
  bc119_commonBox_of_close (fun _ => by simp) (fun _ => by simp)

-- Positive coarse-trifurcation probability at any centre transfers to the origin.
example (L : ℕ) (y : Site 2) (hy : 0 < bern2 {ω | bc61_IsCoarseTrifurcation ω L y}) :
    0 < bern2 {ω | bc61_IsCoarseTrifurcation ω L 0} :=
  bc119_originCoarseTrif_of_yCoarseTrif bern2 bern2_inv L hy

-- The recentred merge at every scale gives the coarse step for Bernoulli(1/2).
example (L : ℕ) (hres : ∀ n : ℕ, bc119_RecenterBoxMerge 2 L n) :
    bc61_CoarseTrifExistence bern2 L :=
  bc119_coarseTrifExistence_of_recenterResidue bern2 bern2_inv bern2_fe L hres

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRecenter

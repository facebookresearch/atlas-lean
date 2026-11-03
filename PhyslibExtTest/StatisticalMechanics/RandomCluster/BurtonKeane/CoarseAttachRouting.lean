/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseAttachRouting

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseAttachRouting`

In the plane, at `L = 3`:
* `bc111_coarsePrecursor_upperLines_emptyWiring` and `bc111_coarseBoxRoute_upperLines_witness`
  give the upper lines (with empty wiring) as a coarse precursor;
* `bc111_coarsePrecursor_forces_boxAdjacency` then gives box sites adjacent to the arm starts;
* `bc111_measurableSet_coarsePrecursor` at explicit sites;
* `bc111_coarseTrifExistence_of_coarseAttach` applied to Bernoulli(1/2) bond percolation.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseAttachRouting

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

-- The upper lines with empty wiring are a coarse precursor at `L = 3`.
example : forceOpenFinset (∅ : Finset (Sym2 (Site 2))) bc60_upperLines ∈
    bc62_CoarseTrifPrecursor 2 3
      (bc57_pt (((3 : ℕ) : ℤ) + 1) 1) (bc57_pt (((3 : ℕ) : ℤ) + 1) 2)
      (bc57_pt (((3 : ℕ) : ℤ) + 1) 3) (bc57_pt ((3 : ℕ) : ℤ) 1) (bc57_pt ((3 : ℕ) : ℤ) 2)
      (bc57_pt ((3 : ℕ) : ℤ) 3) :=
  bc111_coarsePrecursor_upperLines_emptyWiring le_rfl

-- The precursor forces the first arm start to be adjacent to the box.
example : bc57_pt ((3 : ℕ) : ℤ) 1 ∈ bc61_boxAround 2 3 0 ∧
    (hypercubicLattice 2).Adj (bc57_pt ((3 : ℕ) : ℤ) 1) (bc57_pt (((3 : ℕ) : ℤ) + 1) 1) :=
  (bc111_coarsePrecursor_forces_boxAdjacency 3 _ _ _ _ _ _ _
    (bc111_coarsePrecursor_upperLines_emptyWiring le_rfl)).1

-- The existential witness form.
example : ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2) (W : Finset (Sym2 (Site 2))),
    forceOpenFinset W bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 3 a₁ a₂ a₃ b₁ b₂ b₃ :=
  bc111_coarseBoxRoute_upperLines_witness le_rfl

-- Coarse precursors are measurable.
example : MeasurableSet (bc62_CoarseTrifPrecursor 2 3 (bc57_pt 4 1) (bc57_pt 4 2)
    (bc57_pt 4 3) (bc57_pt 3 1) (bc57_pt 3 2) (bc57_pt 3 3)) :=
  bc111_measurableSet_coarsePrecursor 3 _ _ _ _ _ _

-- Coarse attachment at every scale gives the coarse step for Bernoulli(1/2).
example (L : ℕ) (hres : ∀ n : ℕ, bc111_CoarseBoxAttach 2 L n) :
    bc61_CoarseTrifExistence bern2 L :=
  bc111_coarseTrifExistence_of_coarseAttach bern2 bern2_fe L hres

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseAttachRouting

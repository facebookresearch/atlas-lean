/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ReflectedCorridors

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ReflectedCorridors`

* instance: `bcor_corridors_same_right_of_distinct` gives corridors in `B_1` to the right-side
  targets `(1, -1)`, `(1, 0)`, `(1, 1)`;
* the reflection `bcor_corridors_refl` and the swap `bcor_corridors_swap12` transport the library
  witness `bcor_witness` (reflected endpoints computed with `bcor_reflFun_apply`);
* refutation: `bcor_incident_corner_impossible` at `n = 1`;
* `bcor_firstSteps` gives three distinct first steps from the origin for the right-side corridors.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ReflectedCorridors

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Walls

/-- Corridors in `B_1` to the three sites of the right side. -/
theorem right_corridors : bcor_Corridors 1 ![(1 : ℤ), -1] ![(1 : ℤ), 0] ![(1 : ℤ), 1] := by
  exact_mod_cast bcor_corridors_same_right_of_distinct 1 le_rfl (-1) 0 1 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

-- Reflecting and swapping the library witness gives corridors with reflected endpoints.
example : bcor_Corridors 3 ![(-2 : ℤ), -3] ![(3 : ℤ), -1] ![(-3 : ℤ), 2] := by
  have h := bcor_corridors_swap12 (bcor_corridors_refl bcor_witness)
  simpa only [bcor_reflFun_apply, neg_neg] using h

-- Corridors to three mutually adjacent corner sites do not exist.
example : ¬ bcor_Corridors 1 ![(1 : ℤ), 0] ![(1 : ℤ), 1] ![(0 : ℤ), 1] := by
  have h := bcor_incident_corner_impossible 1 le_rfl
  simpa using h

-- The right-side corridors start with three distinct first steps.
example : ∃ a₁ a₂ a₃ : Site 2,
    ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃) ∧ (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) :=
  bcor_firstSteps 1 (by decide) (by decide) (by decide) right_corridors

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ReflectedCorridors

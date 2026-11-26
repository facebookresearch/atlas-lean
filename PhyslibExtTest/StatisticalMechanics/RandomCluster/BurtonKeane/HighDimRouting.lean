/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting`

* `hrHD_rayPt_disjoint_of_ne`: in `ℤ³` the points `2 e₀` and `5 e₁` are different (instance).
* `hrHD_exists_three_independent_axes` for `d = 3`.
* `hrHD_corridor_connected_one_to_L`: opening the corridor along `e₁` in the all-closed
  configuration of `ℤ²` connects `e₁` to `3 e₁` avoiding the origin (instance).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

-- Rays along distinct axes meet only at the origin.
example : (hrHD_rayPt 0 2 : Site 3) ≠ hrHD_rayPt 1 5 :=
  hrHD_rayPt_disjoint_of_ne (by decide) (by norm_num)

-- Three distinct axes in `ℤ³`.
example : ∃ j₁ j₂ j₃ : Fin 3, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ :=
  hrHD_exists_three_independent_axes le_rfl

-- An opened corridor connects `e₁` to `3 e₁` after removing the origin.
example : Connected 2 (removeSite 0 (forceOpenFinset (hrHD_corridorEdges 1 3) fun _ => false))
    (hrHD_rayPt 1 1) (hrHD_rayPt 1 ((3 : ℕ) : ℤ)) :=
  hrHD_corridor_connected_one_to_L _ 1 3 (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting

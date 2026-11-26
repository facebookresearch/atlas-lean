/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxDifferential

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxDifferential`

* `wired_box_differential_inequality_full` on the box of radius `1` in `d = 1`, `q = 2`, `β = 1`;
* `wired_box_differential_inequality` on the box of radius `1` in `d = 2`;
* `activeBox_crossProb_eq_wiredFull`: active and full crossing probabilities agree;
* `boxGraph_edgeSet_nonempty` and `boxActiveEdge_injective` on a concrete box.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxDifferential

open _root_.StatMech _root_.StatMech.OSSS
open Lattice RevealmentConstruction AdaptiveCovLowerGeom
open ActiveBoundaryDifferential FK RevealmentTranslation WiredBoxDifferential

-- The full-measure differential inequality on the one-dimensional box of radius `1`.
example : ∃ c : ℝ, 0 < c ∧
    c * (wiredActiveTheta 1 1 2 1 / wiredActiveDenom 1 1 2 1) ≤
      deriv (wiredFullCrossMass 1 1 2) 1 :=
  wired_box_differential_inequality_full 1 1 le_rfl le_rfl 2 1 1 (by norm_num) one_pos le_rfl

-- The active-edge form of the differential inequality on the two-dimensional box of radius `1`.
example := wired_box_differential_inequality 2 1 (by norm_num) le_rfl 2 1 1 (by norm_num) one_pos
  le_rfl

-- Active and full wired crossing probabilities agree.
example := activeBox_crossProb_eq_wiredFull 2 1 2 1 (by norm_num) one_pos

-- The box with `d, n ≥ 1` has an edge, and the active edge map is injective.
example : Nonempty (boxGraph 2 1).edgeSet ∧ Function.Injective (boxActiveEdge 2 1) :=
  ⟨boxGraph_edgeSet_nonempty 2 1 (by norm_num) le_rfl, boxActiveEdge_injective 2 1⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxDifferential

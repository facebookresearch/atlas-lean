/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellCrossing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellCrossing`

On the `3 × 3` torus:
* `torusCellCrossing_horizontal`: the horizontal edge at `(1, 0)` crosses to the vertical edge at
  `(1, 2)`;
* `torusCellCrossing_vertical`: the vertical edge at `(0, 1)` crosses to the horizontal edge at
  `(2, 1)`;
* `torusCellCrossing_injective` and `torusEdgeCodeEquiv_apply`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellCrossing

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- A horizontal edge crosses to a vertical edge one row down (mod `3`).
example : torusCellCrossing 3 (torusHorizontalEdge 3 1 0) = torusVerticalEdge 3 1 2 := by
  rw [torusCellCrossing_horizontal]
  rfl

-- A vertical edge crosses to a horizontal edge one column left (mod `3`).
example : torusCellCrossing 3 (torusVerticalEdge 3 0 1) = torusHorizontalEdge 3 2 1 := by
  rw [torusCellCrossing_vertical]
  rfl

-- The cell crossing is injective.
example := torusCellCrossing_injective 3

-- The edge-code equivalence decodes codes.
example : torusEdgeCodeEquiv 3 ((0, 0), .horizontal) = torusHorizontalEdge 3 0 0 :=
  torusEdgeCodeEquiv_apply 3 _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellCrossing

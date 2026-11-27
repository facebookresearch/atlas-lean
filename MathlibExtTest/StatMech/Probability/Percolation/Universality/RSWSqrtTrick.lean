/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.RSWSqrtTrick

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.RSWSqrtTrick`

* `rst_rectangle_crossing_pos`, the retained gluing bound. The self-duality family
  (`rst_selfDual_box_crossing_half`, `rst_square_vertical_crossing_half`,
  `rst_selfDual_rectangle_crossing_pos`) was removed: its separation hypothesis fails for
  `[0, 2]²`, so it had no nondegenerate instance.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWSqrtTrick

example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {n : ℤ} {v0 : ℝ} (hn : 0 < n)
    (hL : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent 0 n 0 n))
    (hR : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent n (2 * n) 0 n))
    (hVlb : v0 ≤ μ.real (verticalCrossingEvent n n 0 n)) (hv0 : 0 ≤ v0) :
    v0 / 4 ≤ μ.real (horizontalCrossingEvent 0 (2 * n) 0 n) :=
  rst_rectangle_crossing_pos μ hpa hn hL hR hVlb hv0

end MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWSqrtTrick

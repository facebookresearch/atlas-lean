/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.CrossingReflection

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.CrossingReflection`

* Under `ℙ_{1/2}`, the bottom–top crossing of `[0, 1] × [0, 3]` has the probability of the
  left–right crossing of `[0, 3] × [0, 1]`.
* The diagonal reflection exchanges coordinates.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.CrossingReflection

example : halfMeasure.real (verticalCrossingEvent 0 1 0 3)
    = halfMeasure.real (horizontalCrossingEvent 0 3 0 1) :=
  crf_verticalCrossing_eq_horizontal_swap 0 1 0 3 (measurableSet_horizontalCrossingEvent 0 3 0 1)

example : crf_swap ![1, 2] = ![2, 1] := by
  funext i; fin_cases i <;> simp

end MathlibExtTest.StatMech.Probability.Percolation.Universality.CrossingReflection

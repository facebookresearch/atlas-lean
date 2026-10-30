/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.BXPFromRSW

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.BXPFromRSW`

* Translated crossings have the `ℙ_{1/2}`-probability of the crossing at the origin.
* `⌊k₀ n⌋ = k₀ n`.
* Not covered: `bxr_uniform_seed` and `bxr_boxCrossingProperty` need the RSW bound on `2n × n`
  crossings and positive association of `ℙ_{1/2}`, neither of which is proved in Atlas.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.BXPFromRSW

example : halfMeasure.real (translatedHorizontalCrossingEvent ![5, 7] 4 2)
    = halfMeasure.real (horizontalCrossingEvent 0 4 0 2) :=
  bxr_translatedHorizontalCrossing_invariant _ 4 2 (measurableSet_horizontalCrossingEvent 0 4 0 2)

example : ⌊((3 : ℕ) : ℝ) * ((4 : ℕ) : ℝ)⌋ = 12 := by
  rw [bxr_floor_natMul]; norm_num

end MathlibExtTest.StatMech.Probability.Percolation.Universality.BXPFromRSW

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.BXPAllAspect

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.BXPAllAspect`

* Width monotonicity of crossings: a crossing of `[0, 5] × [0, 2]` contains one of
  `[0, 3] × [0, 2]`, hence the probability is monotone.
* `0 < ⌊ρ n⌋` for `ρ = 3/2`, `n = 1`.
* Not covered: `bxa_boxCrossingProperty_all` and `bxa_boxCrossingProperty_all_of_rsw` (the RSW bound
  `h2box`, the band bound `hband` and positive association of `ℙ_{1/2}` are not proved in Atlas).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.BXPAllAspect

example : horizontalCrossingEvent 0 5 0 2 ⊆ horizontalCrossingEvent 0 3 0 2 :=
  bxa_horizontalCrossingEvent_subset_width (by norm_num) (by norm_num)

example : halfMeasure.real (horizontalCrossingEvent 0 5 0 2)
    ≤ halfMeasure.real (horizontalCrossingEvent 0 3 0 2) :=
  bxa_horizontalCrossing_real_mono_width (by norm_num) (by norm_num)

example : (0 : ℤ) < ⌊(3 / 2 : ℝ) * ((1 : ℕ) : ℝ)⌋ := bxa_zero_lt_floor (by norm_num) le_rfl

end MathlibExtTest.StatMech.Probability.Percolation.Universality.BXPAllAspect

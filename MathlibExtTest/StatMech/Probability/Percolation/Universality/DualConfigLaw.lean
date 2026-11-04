/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.DualConfigLaw

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.DualConfigLaw`

* `dualConfig` pushes `ℙ_p` to `ℙ_{1-p}` (at `p = 0`), `ℙ_{1/2}` is invariant, and `1/2` is the
  unique self-dual density (`0` is not).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.DualConfigLaw

example : Measure.map dualConfig (bernoulliProductMeasure (0 : ℝ≥0) zero_le_one)
    = bernoulliProductMeasure (1 - 0) tsub_le_self :=
  map_dualConfig _ _

example : Measure.map dualConfig (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
    = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one :=
  bernoulliProductMeasure_selfDual_half

example : ¬ (1 - (0 : ℝ≥0) = 0) := by
  rw [selfDual_density_iff _ zero_le_one]; norm_num

example : (1 : ℝ≥0) - 2⁻¹ = 2⁻¹ := one_sub_half

end MathlibExtTest.StatMech.Probability.Percolation.Universality.DualConfigLaw

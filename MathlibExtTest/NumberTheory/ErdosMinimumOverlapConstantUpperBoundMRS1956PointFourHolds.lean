/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapConstantUpperBoundMRS1956PointFourHolds
import MathlibExt.NumberTheory.ErdosMinimumOverlapQuarter

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundMRS1956PointFourHolds

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example : C₁ᵦ ≤ (4 : ℝ) / 10 := upperBound_MRS1956_pointFour_holds

-- The `0.4` bound strictly improves Erdős's `1 / 2` bound.
example : C₁ᵦ < 1 / 2 :=
  lt_of_le_of_lt upperBound_MRS1956_pointFour_holds (by norm_num)

-- Combined with the quarter lower bound, the constant lies in `[1 / 4, 0.4]`.
example : C₁ᵦ ∈ Set.Icc ((1 : ℝ) / 4) ((4 : ℝ) / 10) :=
  ⟨lowerBound_E1955_quarter_holds, upperBound_MRS1956_pointFour_holds⟩

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundMRS1956PointFourHolds

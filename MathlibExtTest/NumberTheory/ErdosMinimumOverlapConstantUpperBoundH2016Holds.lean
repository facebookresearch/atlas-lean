/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstantUpperBoundH2016Holds

/-! Tests for the exact upper bound and its strict two-fifths corollary. -/

@[expose] public section

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundH2016Holds

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example : C₁ᵦ ≤ (380926 : ℝ) / 1000000 := upperBound_H2016_holds

example : C₁ᵦ < (2 : ℝ) / 5 := by
  exact lt_of_le_of_lt upperBound_H2016_holds (by norm_num)

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundH2016Holds

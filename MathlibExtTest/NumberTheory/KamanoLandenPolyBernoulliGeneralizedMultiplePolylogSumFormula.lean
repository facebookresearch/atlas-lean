/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.KamanoLandenPolyBernoulliGeneralizedMultiplePolylogSumFormula

/-! # Tests for the generalized multiple polylogarithm sum formula -/

namespace MathlibExtTest.NumberTheory.KamanoLandenPolyBernoulliGeneralizedMultiplePolylogSumFormula

open MetaMathlibExt

/-- Landen data with `s = 1`, `g₀` with rows `(1, -1)` and `(1, 0)`, and `g₁` the identity. -/
noncomputable abbrev testData : LandenData := ⟨1, 1, 0, ![1], ![0], ![0], ![1]⟩

-- The sum formula for `k = 1`: the sum has the single term for `[1]`.
example : ∑ c : Composition 1,
    (5 : ℝ) ^ (c.length - 1) • generalizedMultiplePolylog testData ![1] ![2] c.blocks =
    generalizedMultiplePolylog testData (![1] + (5 : ℝ) • ![2]) ![3] [1] :=
  generalizedMultiplePolylog_sum_formula testData ![1] ![2] ![3] 5 1 (by decide)

-- The sum formula for `k = 2`: the terms for `[2]` and `[1, 1]`.
example : ∑ c : Composition 2,
    (3 : ℝ) ^ (c.length - 1) • generalizedMultiplePolylog testData ![1] ![2] c.blocks =
    generalizedMultiplePolylog testData (![1] + (3 : ℝ) • ![2]) ![0] [2] :=
  generalizedMultiplePolylog_sum_formula testData ![1] ![2] ![0] 3 2 (by decide)

end MathlibExtTest.NumberTheory.KamanoLandenPolyBernoulliGeneralizedMultiplePolylogSumFormula

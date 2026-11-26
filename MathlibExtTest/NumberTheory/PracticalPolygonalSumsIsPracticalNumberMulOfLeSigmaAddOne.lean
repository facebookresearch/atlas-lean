/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PracticalPolygonalSumsIsPracticalNumberMulOfLeSigmaAddOne
import Mathlib.Tactic.IntervalCases

/-! # Tests for products of a practical number with small factors -/

namespace MathlibExtTest.NumberTheory.PracticalPolygonalSumsIsPracticalNumberMulOfLeSigmaAddOne

open MetaMathlibExt ArithmeticFunction

-- 6 is practical, with explicit divisor subsets.
theorem isPracticalNumber_six : IsPracticalNumber 6 := by
  refine ⟨by decide, ?_⟩
  intro m hm1 hm6
  interval_cases m
  · exact ⟨{1}, by decide, by decide⟩
  · exact ⟨{2}, by decide, by decide⟩
  · exact ⟨{3}, by decide, by decide⟩
  · exact ⟨{1, 3}, by decide, by decide⟩
  · exact ⟨{2, 3}, by decide, by decide⟩
  · exact ⟨{6}, by decide, by decide⟩

-- σ(6) = 1 + 2 + 3 + 6 = 12.
theorem sigma_one_six : sigma 1 6 = 12 := by decide

-- A concrete product: 6 * 5 is practical since 5 ≤ σ(6) + 1.
example : IsPracticalNumber (6 * 5) :=
  isPracticalNumber_mul_of_le_sigma_add_one 6 5 isPracticalNumber_six (by decide)
    (by simp [sigma_one_six])

-- Every multiple of 6 by a factor from 1 to σ(6) + 1 = 13 is practical.
example (n : ℕ) (hn : 0 < n) (hnm : n ≤ 13) : IsPracticalNumber (6 * n) :=
  isPracticalNumber_mul_of_le_sigma_add_one 6 n isPracticalNumber_six hn (by
    rw [sigma_one_six]
    omega)

end MathlibExtTest.NumberTheory.PracticalPolygonalSumsIsPracticalNumberMulOfLeSigmaAddOne

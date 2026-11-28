/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.PracticalPolygonalSumsEventuallyTwo

namespace MetaMathlibExt

-- The smallest allowed value of `s` gives sums with two squares.
example : ∃ N : ℕ, ∀ n > N, ∃ q x y : ℕ,
    IsPracticalNumber q ∧ n = q + x ^ 2 + y ^ 2 := by
  simpa only [Nat.polygonalNumber_four] using eventually_practical_add_two_polygonal 4 (by decide)

-- At an odd value of `s`, both summands have the pentagonal closed form.
example : ∃ N : ℕ, ∀ n > N, ∃ q x y : ℕ,
    IsPracticalNumber q ∧ n = q + (3 * x ^ 2 - x) / 2 + (3 * y ^ 2 - y) / 2 := by
  simpa only [Nat.polygonalNumber_five] using eventually_practical_add_two_polygonal 5 (by decide)

-- Explicit square witnesses: 17 = 4 + 4 + 9. Verify each divisor sum for 4.
example : IsPracticalNumber 4 ∧ 17 = 4 + Nat.polygonalNumber 4 2 + Nat.polygonalNumber 4 3 := by
  constructor
  · rw [isPracticalNumber_iff]
    refine ⟨by decide, fun m hm hle ↦ ?_⟩
    interval_cases m
    · exact ⟨{1}, by decide, by decide⟩
    · exact ⟨{2}, by decide, by decide⟩
    · exact ⟨{1, 2}, by decide, by decide⟩
    · exact ⟨{4}, by decide, by decide⟩
  · rw [Nat.polygonalNumber_four, Nat.polygonalNumber_four]

-- Explicit pentagonal witnesses: 12 = 6 + 1 + 5. Verify each divisor sum for 6.
example : IsPracticalNumber 6 ∧ 12 = 6 + Nat.polygonalNumber 5 1 + Nat.polygonalNumber 5 2 := by
  constructor
  · rw [isPracticalNumber_iff]
    refine ⟨by decide, fun m hm hle ↦ ?_⟩
    interval_cases m
    · exact ⟨{1}, by decide, by decide⟩
    · exact ⟨{2}, by decide, by decide⟩
    · exact ⟨{3}, by decide, by decide⟩
    · exact ⟨{1, 3}, by decide, by decide⟩
    · exact ⟨{2, 3}, by decide, by decide⟩
    · exact ⟨{6}, by decide, by decide⟩
  · rw [Nat.polygonalNumber_one, Nat.polygonalNumber_at_two 5 (by decide)]

end MetaMathlibExt

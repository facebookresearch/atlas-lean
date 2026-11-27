/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.A005717ZeroDensity

/-! # Tests for the zero density of A005717 modulo a prime -/

open MetaMathlibExt

namespace MetaMathlibExtTest.A005717ZeroDensity

private theorem centralTrinomial_values :
    centralTrinomial 1 1 0 = 1 ∧ centralTrinomial 1 1 1 = 1 ∧ centralTrinomial 1 1 2 = 3 ∧
      centralTrinomial 1 1 3 = 7 ∧ centralTrinomial 1 1 4 = 19 := by
  simpa [List.range_succ] using centralTrinomial_one_one_values

-- Modulo 3 the digit 2 has T₂ = 3, so A005717 vanishes modulo 3 with density one.
example : ({n | a005717 n ≡ 0 [ZMOD 3]} : Set ℕ).HasDensity 1 := by
  have h := (a005717_zero_density 3 Nat.prime_three).1
    ⟨2, by norm_num, by rw [centralTrinomial_values.2.2.1]; decide⟩
  simpa using h

-- At p = 2 neither case applies: T₀ = T₁ = 1 are odd, and the second case needs p > 2.
example : ¬∃ r < 2, centralTrinomial 1 1 r ≡ 0 [ZMOD 2] := by
  obtain ⟨h0, h1, -⟩ := centralTrinomial_values
  rintro ⟨r, hr, h⟩
  interval_cases r
  · rw [h0] at h
    exact absurd h (by decide)
  · rw [h1] at h
    exact absurd h (by decide)

-- Modulo 5 the coefficients T₀, …, T₄ are 1, 1, 3, 2, 4, so none vanishes. Only m = 2 satisfies
-- T_m ≡ T₄ T_{m+1} and only m = 0 satisfies T_m ≡ T_{m+1}, so the density is
-- (1 + 5 · 1) / (4 · 6) = 1/4, which attains the lower bound 1/(p - 1).
example : ({n | a005717 n ≡ 0 [ZMOD 5]} : Set ℕ).HasDensity (1 / 4) ∧
    (1 : ℝ) / 4 = 1 / ((5 - 1 : ℕ) : ℝ) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := centralTrinomial_values
  have hT : ∀ r < 5, ¬(centralTrinomial 1 1 r ≡ 0 [ZMOD (5 : ℕ)]) := by
    intro r hr
    interval_cases r <;> simp [h0, h1, h2, h3, h4, Int.ModEq]
  have h := ((a005717_zero_density 5 Nat.prime_five).2 hT (by norm_num)).1
  have hrange : Finset.range (5 - 1) = {0, 1, 2, 3} := by decide
  simp only [hrange, Finset.filter_insert, Finset.filter_singleton, Nat.reduceSub,
    Nat.reduceAdd, h0, h1, h2, h3, h4] at h
  norm_num [Int.ModEq] at h
  exact ⟨by simpa [Int.ModEq] using h, by norm_num⟩

end MetaMathlibExtTest.A005717ZeroDensity

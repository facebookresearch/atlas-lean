/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisibilityRunsGibonacciGeneralizedTribonacciGrowthBounds
import MathlibExt.NumberTheory.DivRunCountFour
import MathlibExt.NumberTheory.DivisibilityRuns
import MathlibExt.NumberTheory.GeneralizedTribonacciBasis
import MathlibExt.NumberTheory.DivisibilityRunsGibonacciNumberEqFib

namespace MathlibExtTest.NumberTheory.DivisibilityRunsGibonacciGeneralizedTribonacciGrowthBounds

open MetaMathlibExt

/-- The Lucas-like Gibonacci sequence `2, 1` satisfies the upper bound at `n = 5`. -/
example : |(gibonacciNumber 2 1 5 : ℝ)|
    ≤ (|((2 : ℤ) : ℝ)| + |((1 : ℤ) : ℝ)|) * Real.goldenRatio ^ 5 :=
  gibonacci_generalizedTribonacci_growth_bounds.1 2 1 5

/-- The value above is `11`, so the bound reads `11 ≤ 3 * φ ^ 5`. -/
example : gibonacciNumber 2 1 5 = 11 := by decide

/-- Corollary: the lower bound for the Lucas-like initial values above its threshold. -/
example : ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∀ n : ℕ,
    c₁ * (Real.log 3 + 1) ≤ (n : ℝ) →
      c₀ * Real.goldenRatio ^ (n + 1) / 3 ≤ |(gibonacciNumber 2 1 n : ℝ)| := by
  obtain ⟨c₀, c₁, hc₀, hc₁, h⟩ := gibonacci_generalizedTribonacci_growth_bounds.2.1
  refine ⟨c₀, c₁, hc₀, hc₁, fun n hn => ?_⟩
  have hS : |((2 : ℤ) : ℝ)| + |((1 : ℤ) : ℝ)| = 3 := by norm_num
  have hth := h 2 1 (by decide) n (by rw [hS]; exact hn)
  rwa [hS] at hth

/-- The generalized Tribonacci sequence `1, 2, -1` satisfies the upper bound at `n = 4`. -/
example (τ : ℝ) (hτ : τ ^ 3 = τ ^ 2 + τ + 1) :
    |(generalizedTribonacci 1 2 (-1) 4 : ℝ)|
      ≤ (|((1 : ℤ) : ℝ)| + |((2 : ℤ) : ℝ)| + |(((-1 : ℤ)) : ℝ)|) * τ ^ 4 :=
  gibonacci_generalizedTribonacci_growth_bounds.2.2 τ hτ 1 2 (-1) 4

/-- The value above is `3`, so the bound reads `3 ≤ 4 * τ ^ 4`. -/
example : generalizedTribonacci 1 2 (-1) 4 = 3 := by decide

end MathlibExtTest.NumberTheory.DivisibilityRunsGibonacciGeneralizedTribonacciGrowthBounds

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasWeightedPowerSumExistsRemaindersWeightedPowerSum
import Mathlib.Tactic.NormNum

/-!
# Tests for weighted Lucas power-sum remainders

Concrete weighted Fibonacci sums exercise the linear case, the mixed-exponent case, and
the case where both exponents are at least two.
-/

namespace MathlibExtTest.NumberTheory.Recurrences
namespace LucasWeightedPowerSumExistsRemaindersWeightedPowerSum

open MetaMathlibExt

example :
    let α : ℝ := (1 + Real.sqrt 5) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < 16 * α ^ (-4 : ℝ) ∧ |R₂| < α ^ (-8 : ℝ) := by
  have hsol : ∑ j ∈ Finset.Icc (1 : ℕ) 4, (j : ℤ) * lucasU fibonacciLucasParams j ^ 1 =
      lucasU fibonacciLucasParams 8 ^ 1 := by decide
  obtain ⟨R₁, R₂, hR₁, hR₂, _⟩ := exists_remainders_weighted_power_sum
    fibonacciLucasParams (Or.inr rfl) (by decide) (by decide)
    (n := 8) (k := 4) (p := 1) (q := 1) (by decide) (by decide) (by decide) (by decide) hsol
  refine ⟨R₁, R₂, ?_, ?_⟩
  · convert hR₁ using 1
    norm_num [fibonacciLucasParams]
  · convert hR₂ using 1
    norm_num [fibonacciLucasParams]

example :
    let α : ℝ := (1 + Real.sqrt 5) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < 9 * α ^ (-3 : ℝ) ∧ |R₂| < 1 ∧
      (5 : ℝ) ^ ((1 : ℝ) / 2) * (3 * α - 4) / (α - 1) ^ 2 * α ^ 4 - α ^ 8 =
        5 * R₂ - 5 * R₁ - (5 : ℝ) ^ ((1 : ℝ) / 2) * α / (α - 1) ^ 2 := by
  have hsol : ∑ j ∈ Finset.Icc (1 : ℕ) 3, (j : ℤ) * lucasU fibonacciLucasParams j ^ 1 =
      lucasU fibonacciLucasParams 4 ^ 2 := by decide
  obtain ⟨R₁, R₂, hR₁, hR₂, hE⟩ := exists_remainders_weighted_power_sum
    fibonacciLucasParams (Or.inr rfl) (by decide) (by decide)
    (n := 4) (k := 3) (p := 1) (q := 2) (by decide) (by decide) (by decide) (by decide) hsol
  refine ⟨R₁, R₂, ?_, ?_, ?_⟩
  · convert hR₁ using 1
    norm_num [fibonacciLucasParams]
  · convert hR₂ using 1
    norm_num [fibonacciLucasParams]
  · convert hE using 1 <;> norm_num [fibonacciLucasParams]

example :
    let α : ℝ := (1 + Real.sqrt 5) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < 9 * α ^ (3 : ℝ) ∧ |R₂| < α ^ (4 : ℝ) := by
  have hsol : ∑ j ∈ Finset.Icc (1 : ℕ) 3, (j : ℤ) * lucasU fibonacciLucasParams j ^ 3 =
      lucasU fibonacciLucasParams 4 ^ 3 := by decide
  obtain ⟨R₁, R₂, hR₁, hR₂, _⟩ := exists_remainders_weighted_power_sum
    fibonacciLucasParams (Or.inr rfl) (by decide) (by decide)
    (n := 4) (k := 3) (p := 3) (q := 3) (by decide) (by decide) (by decide) (by decide) hsol
  refine ⟨R₁, R₂, ?_, ?_⟩
  · convert hR₁ using 1
    norm_num [fibonacciLucasParams]
  · convert hR₂ using 1
    norm_num [fibonacciLucasParams]

end LucasWeightedPowerSumExistsRemaindersWeightedPowerSum
end MathlibExtTest.NumberTheory.Recurrences

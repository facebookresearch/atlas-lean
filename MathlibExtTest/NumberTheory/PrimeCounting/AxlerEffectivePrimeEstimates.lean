/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.AxlerEffectivePrimeEstimates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Tests for Axler's truncated series bound
-/

namespace MetaMathlibExt

-- At order three the convolution uses three different earlier coefficients.
example (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hpos : ∀ x : ℝ, x₀ ≤ x → 0 < 2 * Real.log x - 4 - 4 / Real.log x - 4 / Real.log x ^ 2)
    (hlow : ∀ x : ℝ, x₀ ≤ x →
      x / (2 * Real.log x - 4 - 4 / Real.log x - 4 / Real.log x ^ 2) <
        (Nat.primeCounting ⌊x⌋₊ : ℝ))
    (x : ℝ) (hx : x₀ ≤ x) :
    x / (2 * Real.log x) + x / Real.log x ^ 2 + 3 * x / Real.log x ^ 3 + 9 * x / Real.log x ^ 4 <
      (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  let a (i : ℕ) : ℝ := if i = 0 then 2 else -4
  let b (k : ℕ) : ℝ := if k = 0 then 1 / 2 else 3 ^ (k - 1)
  have h₃ : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hden (y : ℝ) :
      a 0 * Real.log y + ∑ i ∈ Finset.Icc 1 3, a i / Real.log y ^ (i - 1) =
        2 * Real.log y - 4 - 4 / Real.log y - 4 / Real.log y ^ 2 := by
    rw [h₃]
    norm_num [a]
    ring
  have h := series_lt_primeCounting_of_lt_primeCounting 3 (by decide) a b (by norm_num [a])
    (by intro i hi; rw [h₃] at hi; fin_cases hi <;> norm_num [a]) x₀ hx₀
    (fun y hy ↦ hden y ▸ hpos y hy) (fun y hy ↦ hden y ▸ hlow y hy) (by norm_num [a, b])
    (by
      intro k hk
      rw [h₃] at hk
      fin_cases hk <;>
        norm_num [a, b, h₃, show Finset.Icc 1 2 = {1, 2} by decide]) x hx
  convert h using 1
  norm_num [b, Finset.sum_range_succ]
  ring

end MetaMathlibExt

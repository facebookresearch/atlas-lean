/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ChebyshevCPartialSum

/-! # Tests for the monic Chebyshev partial sums -/

open MetaMathlibExt Polynomial

-- The empty partial sum contributes one to the generating function.
example : (PowerSeries.mk chebyshevCPartialSum).constantCoeff = 1 := by
  simp [chebyshevCPartialSum]

-- At X = 0 the denominator is 1 + t², so the linear term comes entirely from the numerator.
example :
    (1 + PowerSeries.X ^ 2) * PowerSeries.mk (fun n => (chebyshevCPartialSum n).eval 0) =
      (1 + PowerSeries.X : PowerSeries ℤ) := by
  have h : PowerSeries.map (evalRingHom (0 : ℤ)) (PowerSeries.mk chebyshevCPartialSum) =
      PowerSeries.mk (fun n => (chebyshevCPartialSum n).eval 0) := by
    apply PowerSeries.ext
    intro n
    simp
  simpa [h] using congrArg (PowerSeries.map (evalRingHom (0 : ℤ)))
    chebyshevCPartialSum_generatingFunction

-- At the first admissible index the predecessor is the constant polynomial one.
example : chebyshevCPartialSum 2 = X ^ 2 + X - 1 := by
  rw [chebyshevCPartialSum_recurrence 1 (by decide), chebyshevCPartialSum_one_two.1,
    chebyshevCPartialSum_zero]
  ring

-- At the boundary `n = 1` the expansion is `X + 1`, matching `chebyshevCPartialSum_one_two`.
example : chebyshevCPartialSum 1 = X + 1 := by
  rw [chebyshevCPartialSum_eq_binomial_sum 1 le_rfl]
  simp

-- The hypothesis `1 ≤ n` is needed: at `n = 0` truncated subtraction makes the right side
-- `1 + 1 = 2`, while `F₀ = 1`.
example :
    chebyshevCPartialSum 0 ≠
      ∑ m ∈ Finset.range (0 / 2 + 1),
          (-1 : ℤ[X]) ^ m * ((0 - m).choose m : ℤ[X]) * X ^ (0 - 2 * m) +
        ∑ m ∈ Finset.range ((0 - 1) / 2 + 1),
          (-1 : ℤ[X]) ^ m * ((0 - m - 1).choose m : ℤ[X]) * X ^ (0 - 2 * m - 1) := by
  rw [chebyshevCPartialSum_zero]
  norm_num

-- At `n = 4` both sums have nontrivial binomial coefficients: `F₄ = X⁴ + X³ - 3X² - 2X + 1`.
example : chebyshevCPartialSum 4 = X ^ 4 + X ^ 3 - 3 * X ^ 2 - 2 * X + 1 := by
  rw [chebyshevCPartialSum_eq_binomial_sum 4 (by decide)]
  simp [Finset.sum_range_succ]
  ring

-- At `X = 2` every `T̄_k` equals `2`, so the two binomial sums add up to `2 * n + 1`.
example (n : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ Finset.range (n / 2 + 1),
          (-1 : ℤ[X]) ^ m * ((n - m).choose m : ℤ[X]) * X ^ (n - 2 * m) +
        ∑ m ∈ Finset.range ((n - 1) / 2 + 1),
          (-1 : ℤ[X]) ^ m * ((n - m - 1).choose m : ℤ[X]) * X ^ (n - 2 * m - 1)).eval 2 =
      2 * (n : ℤ) + 1 := by
  rw [← chebyshevCPartialSum_eq_binomial_sum n hn]
  simp [chebyshevCPartialSum, eval_finsetSum]
  ring

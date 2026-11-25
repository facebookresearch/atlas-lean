/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciCentralSeries

open Real

namespace MetaMathlibExt.pi_sq_eq_fibonacci_central_series.Tests

-- Check both identities with the original factorial powers and indices.
example :
    Real.pi ^ 2 = 250 / (8 * √5) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (Nat.fib (2 * k + 2) : ℝ) / ((2 * k + 2).factorial : ℝ) ∧
      Real.pi ^ 2 = 250 / (25 - 4 * √5) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (Nat.fib (2 * k + 1) : ℝ) / ((2 * k + 2).factorial : ℝ) :=
  pi_sq_eq_fibonacci_central_series

-- The total sums in the identities represent convergent series.
example :
    Summable (fun k : ℕ ↦ ((k.factorial ^ 2 : ℕ) : ℝ) * Nat.fib (2 * k + 2) /
      (2 * k + 2).factorial) ∧
    Summable (fun k : ℕ ↦ ((k.factorial ^ 2 : ℕ) : ℝ) * Nat.fib (2 * k + 1) /
      (2 * k + 2).factorial) :=
  ⟨hasSum_even_odd.1.summable, hasSum_even_odd.2.summable⟩

end MetaMathlibExt.pi_sq_eq_fibonacci_central_series.Tests

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.Recurrences.FibonacciBrousseauSums

namespace MetaMathlibExt

-- The constant weight at step one gives the standard partial sum, including the empty sum.
example (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (Nat.fib i : ℚ) = (Nat.fib (n + 2) : ℚ) - 1 := by
  have hstep : (Nat.fib (n + 2) : ℚ) = (Nat.fib n : ℚ) + Nat.fib (n + 1) := by
    exact_mod_cast Nat.fib_add_two
  simpa [lucasNumber, brousseauCoeff_zero, hstep, add_comm] using
    fibonacci_brousseau_sum_mul_odd 1 (by decide) n 0

-- The linear weight at step three uses both endpoints and a nonzero correction.
example : ∑ i ∈ Finset.Icc (1 : ℕ) 2, (i : ℚ) * Nat.fib (3 * i) = 18 := by
  have h := fibonacci_brousseau_sum_mul_odd 3 (by decide) 2 1
  norm_num [lucasNumber, brousseauCoeff_one, Nat.fib] at h ⊢
  linarith

end MetaMathlibExt

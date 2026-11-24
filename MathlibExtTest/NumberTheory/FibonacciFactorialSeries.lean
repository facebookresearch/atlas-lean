/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciFactorialSeries
import Mathlib.Tactic.Ring

open Polynomial Real

namespace MetaMathlibExt.pi_sq_eq_fibonacci_factorial_series.Tests

private noncomputable def p : ℕ → ℤ[X]
  | 0 => 17
  | 1 => 1
  | n + 2 => (2 * X + C (2 * (n + 1 : ℕ) + 1 : ℤ)) * (2 * X + C (2 * (n + 1 : ℕ) + 2 : ℤ)) *
      p (n + 1) - (X + 1) ^ 2 * (p (n + 1)).comp (X + 1)

private noncomputable def a : ℕ → ℝ
  | 0 => -(8 * √5) / 250
  | 1 => (25 - 4 * √5) / 250
  | n + 2 => a (n + 1) + a n

private noncomputable def b : ℕ → ℝ
  | 0 | 1 => 0
  | n + 2 => b (n + 1) + b n + (-1) ^ (n + 2) * (((p (n + 1)).eval 0 : ℤ) : ℝ) /
      (2 * (n + 1)).factorial

-- The initial even-index identity holds with p₀ = 17.
example : π ^ 2 = -(∑' k : ℕ, (k.factorial : ℝ) ^ 2 * Nat.fib (2 * k + 2) /
    (2 * k + 2).factorial) / (-(8 * √5) / 250) := by
  have h := pi_sq_eq_fibonacci_factorial_series p rfl (by rintro (_ | n) hn <;> first | rfl | omega)
    a rfl rfl (by rintro (_ | n) hn <;> first | rfl | omega)
    b rfl rfl (by rintro (_ | n) hn <;> first | rfl | omega) (n := 1) (by decide)
  simpa [p, a, b] using h.1

-- The first recurrence step has a nonzero boundary term, b₂ = 1/2.
example : π ^ 2 = (1 / 2 - ∑' k : ℕ, (k.factorial : ℝ) ^ 2 *
    (3 * (k : ℝ) ^ 2 + 12 * k + 11) * Nat.fib (2 * k + 1) / (2 * k + 4).factorial) /
    ((25 - 12 * √5) / 250) := by
  have h := pi_sq_eq_fibonacci_factorial_series p rfl (by rintro (_ | n) hn <;> first | rfl | omega)
    a rfl rfl (by rintro (_ | n) hn <;> first | rfl | omega)
    b rfl rfl (by rintro (_ | n) hn <;> first | rfl | omega) (n := 2) (by decide)
  have hp (k : ℕ) : (((p 2).eval (k : ℤ) : ℤ) : ℝ) = 3 * (k : ℝ) ^ 2 + 12 * k + 11 := by
    norm_num [p, eval_sub, eval_mul, eval_add, eval_pow]
    ring
  have ha : a 2 = (25 - 12 * √5) / 250 := by rw [a, a, a]; ring
  have hb : b 2 = 1 / 2 := by norm_num [b, p, Nat.factorial]
  simpa [hp, ha, hb, sub_eq_add_neg, show (-1 : ℝ) ^ 3 = -1 by norm_num] using h.2

end MetaMathlibExt.pi_sq_eq_fibonacci_factorial_series.Tests

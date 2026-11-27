/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.DivisibilityRunsGibonacciNumberEqFib

namespace MathlibExtTest.NumberTheory.DivisibilityRunsGibonacciNumberEqFib

open MetaMathlibExt

/-- The Lucas numbers start `2, 1`; the formula gives `L₅ = F₄ * 2 + F₅ * 1 = 3 * 2 + 5 = 11`. -/
example : gibonacciNumber 2 1 5 = 11 := by
  rw [gibonacciNumber_eq_fib 2 1 5 (by norm_num)]
  decide

/-- The formula agrees with direct evaluation of the recurrence at a concrete index. -/
example : gibonacciNumber 3 (-7) 6 =
    (Nat.fib 5 : ℤ) * 3 + (Nat.fib 6 : ℤ) * (-7) := by
  rw [gibonacciNumber_eq_fib 3 (-7) 6 (by norm_num)]

/-- Corollary: initial values `0, 1` recover the Fibonacci numbers for `n ≥ 1`. -/
example (n : ℕ) (hn : 1 ≤ n) : gibonacciNumber 0 1 n = (Nat.fib n : ℤ) := by
  simp [gibonacciNumber_eq_fib 0 1 n hn]

/-- Corollary: the Gibonacci sequence is linear in its initial values. -/
example (x y x' y' : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    gibonacciNumber (x + x') (y + y') n = gibonacciNumber x y n + gibonacciNumber x' y' n := by
  rw [gibonacciNumber_eq_fib _ _ n hn, gibonacciNumber_eq_fib _ _ n hn,
    gibonacciNumber_eq_fib _ _ n hn]
  ring

/-- Corollary: if both initial values are divisible by `d`, so is every later term. -/
example (d x y : ℤ) (hx : d ∣ x) (hy : d ∣ y) (n : ℕ) (hn : 1 ≤ n) :
    d ∣ gibonacciNumber x y n := by
  rw [gibonacciNumber_eq_fib x y n hn]
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨(Nat.fib (n - 1) : ℤ) * a + (Nat.fib n : ℤ) * b, by ring⟩

end MathlibExtTest.NumberTheory.DivisibilityRunsGibonacciNumberEqFib

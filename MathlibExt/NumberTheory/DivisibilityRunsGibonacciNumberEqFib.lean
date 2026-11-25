/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GibonacciNumber
import Mathlib.Tactic.Ring

/-!
# Gibonacci numbers in terms of Fibonacci numbers

Every Gibonacci number is an integer combination of its two initial values with Fibonacci
coefficients: $P_n = F_{n-1} x + F_n y$ for $n \ge 1$. This is Proposition 1 of Nicholas Smirnov,
*Finite Divisibility Runs Between Generalized Fibonacci and Tribonacci Sequences*.
-/

namespace MetaMathlibExt

/-- Two consecutive Gibonacci numbers in terms of Fibonacci numbers, proved jointly so that the
induction can use the two-term recurrence. -/
private theorem gibonacciNumber_succ_eq_fib (x y : ℤ) (m : ℕ) :
    gibonacciNumber x y (m + 1) = (Nat.fib m : ℤ) * x + (Nat.fib (m + 1) : ℤ) * y ∧
      gibonacciNumber x y (m + 2) = (Nat.fib (m + 1) : ℤ) * x + (Nat.fib (m + 2) : ℤ) * y := by
  induction m with
  | zero => simp [gibonacciNumber, add_comm]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : gibonacciNumber x y (n + 1 + 2) =
        gibonacciNumber x y (n + 2) + gibonacciNumber x y (n + 1) := rfl
    rw [hrec, ih.1, ih.2, show n + 1 + 2 = (n + 1) + 2 from rfl, Nat.fib_add_two (n := n + 1),
      Nat.fib_add_two (n := n)]
    push_cast
    ring

/-- **Gibonacci numbers in terms of Fibonacci numbers.** Let $x, y$ be integers, let
$(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and $P_1 = y$, and let $(F_n)_{n \ge 0}$
be the Fibonacci sequence with $F_0 = 0$ and $F_1 = 1$. For every $n \ge 1$,
$P_n = F_{n-1}\,x + F_n\,y$.

The paper indexes $P$ from $1$ and states this as $P_n = F_{n-2}\,x + F_{n-1}\,y$ for $n \ge 2$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 1
(`integers-2026-A122-prop-1`). -/
public theorem gibonacciNumber_eq_fib (x y : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    gibonacciNumber x y n = (Nat.fib (n - 1) : ℤ) * x + (Nat.fib n : ℤ) * y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using (gibonacciNumber_succ_eq_fib x y m).1

end MetaMathlibExt

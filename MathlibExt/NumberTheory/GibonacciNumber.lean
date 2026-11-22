/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic

/-!
# Gibonacci numbers

This file formalizes the generalized Fibonacci sequence used by Dan Guyer and
aBa Mbirika, *GCD of Sums of k Consecutive Fibonacci, Lucas, and Generalized
Fibonacci Numbers*:
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Mbirika/mb5.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Gibonacci numbers.** For integers $G_0$ and $G_1$, the Gibonacci sequence with initial
values $G_0$ and $G_1$ is the integer sequence $(G_n)_{n \ge 0}$ that starts with $G_0, G_1$ and
satisfies $G_{n+2} = G_{n+1} + G_n$ for every $n \ge 0$. -/
def gibonacciNumber (G₀ G₁ : ℤ) : ℕ → ℤ
  | 0 => G₀
  | 1 => G₁
  | n + 2 => gibonacciNumber G₀ G₁ (n + 1) + gibonacciNumber G₀ G₁ n

/-- **Gibonacci numbers starting from 0 and 1 are the Fibonacci numbers.** For every natural
number $n$, the $n$-th Gibonacci number with initial values $G_0 = 0$ and $G_1 = 1$ equals the
$n$-th Fibonacci number $F_n$ (where $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$). -/
theorem gibonacci_zero_one_eq_fib (n : ℕ) :
    gibonacciNumber 0 1 n = (Nat.fib n : ℤ) := by
  have h : ∀ m : ℕ, gibonacciNumber 0 1 m = (Nat.fib m : ℤ) ∧
      gibonacciNumber 0 1 (m + 1) = (Nat.fib (m + 1) : ℤ) := by
    intro m
    induction m with
    | zero => simp [gibonacciNumber, Nat.fib_zero, Nat.fib_one]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hindex : n + 1 + 1 = n + 2 := rfl
      rw [hindex]
      simp only [gibonacciNumber, Nat.fib_add_two, Nat.cast_add, ih.1, ih.2, add_comm]
  exact (h n).1

end MetaMathlibExt

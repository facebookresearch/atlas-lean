/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence

/-!
# A Lucas–Fibonacci identity for base-phi expansions

This file proves $F_n + 3F_{n+1} = L_{n+2}$ for every natural number $n$, using
`lucasNumber_add_one_eq_fib_add_fib` and the Fibonacci recurrence. This is Lemma 9 of
F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24,
where the identity counts integers in certain intervals of base-phi expansions.
-/

namespace MetaMathlibExt

/-- **Lucas numbers from Fibonacci numbers.** For every natural number $n$,
$F_n + 3F_{n+1} = L_{n+2}$, where $F_j$ is the $j$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$) and
$L_j$ is the $j$-th Lucas number ($L_0 = 2$, $L_1 = 1$).

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 9 (`integers-2024-A24-lem-9`). -/
public theorem fib_add_three_mul_fib_succ_eq_lucasNumber (n : ℕ) :
    Nat.fib n + 3 * Nat.fib (n + 1) = lucasNumber (n + 2) := by
  rw [lucasNumber_add_one_eq_fib_add_fib (n + 1)]
  change Nat.fib n + 3 * Nat.fib (n + 1) = Nat.fib (n + 1) + Nat.fib (n + 3)
  have hf₀ : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have hf₁ : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  omega

end MetaMathlibExt

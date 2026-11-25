/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

/-- **Lucas numbers from Fibonacci numbers.** For every natural number $n$,
$F_n + 3F_{n+1} = L_{n+2}$, where $F_j$ is the $j$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$) and
$L_j$ is the $j$-th Lucas number ($L_0 = 2$, $L_1 = 1$).

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 9 (`integers-2024-A24-lem-9`). -/
public theorem fib_add_three_mul_fib_succ_eq_lucasNumber (n : ℕ) :
    Nat.fib n + 3 * Nat.fib (n + 1) = lucasNumber (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih₀ ih₁ =>
    have hf₀ : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have hf₁ : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have hL : lucasNumber (n + 4) = lucasNumber (n + 3) + lucasNumber (n + 2) := rfl
    change Nat.fib (n + 2) + 3 * Nat.fib (n + 3) = lucasNumber (n + 4)
    rw [hL, ← ih₁, ← ih₀, hf₁, hf₀]
    omega

end MetaMathlibExt

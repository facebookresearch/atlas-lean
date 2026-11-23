/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-! # Oresme–Fibonacci congruence modulo 5 -/

namespace MetaMathlibExt

/-- **Oresme–Fibonacci congruence modulo 5.** Let $F_n$ denote the Fibonacci numbers, with
$F_0 = 0$ and $F_1 = 1$. For every natural number $n$, $2^{n-1} F_n \equiv n \pmod 5$, where at
$n = 0$ the exponent $n - 1$ is taken to be $0$ (both sides are then $0$).

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 4.2 (`fq-2024-cookbacon061124-cor-4.2`). -/
public theorem two_pow_pred_mul_fib_modEq_five (n : ℕ) :
    2 ^ (n - 1) * Nat.fib n ≡ n [MOD 5] := by
  obtain _ | n := n
  · decide
  change 2 ^ n * Nat.fib (n + 1) ≡ n + 1 [MOD 5]
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih₀ ih₁ =>
    calc
      2 ^ (n + 2) * Nat.fib (n + 3) =
          4 * (2 ^ n * Nat.fib (n + 1)) + 2 * (2 ^ (n + 1) * Nat.fib (n + 2)) := by
            rw [Nat.fib_add_two (n := n + 1)]
            simp only [pow_succ]
            ring
      _ ≡ 4 * (n + 1) + 2 * (n + 2) [MOD 5] := (ih₀.mul_left 4).add (ih₁.mul_left 2)
      _ ≡ n + 3 [MOD 5] := by unfold Nat.ModEq; omega

end MetaMathlibExt

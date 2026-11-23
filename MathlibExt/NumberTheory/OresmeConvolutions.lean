/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Fibonacci–Oresme convolution and congruence -/

namespace MetaMathlibExt

/-- **Fibonacci–Oresme convolution.** Let $F_m$ denote the Fibonacci numbers, with $F_0 = 0$,
$F_1 = 1$ and $F_{m+2} = F_{m+1} + F_m$, and let $O_m = m/2^m$ denote the Oresme numbers. For
every natural number $n$,
$\sum_{k=0}^{n} F_k O_{n-k} = \frac{2}{5} F_{n+1} - \frac{2(n+1)}{5 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 4.1 (`fq-2024-cookbacon061124-prop-4.1`). -/
public theorem fib_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Nat.fib k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 5 * (Nat.fib (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) / (5 * 2 ^ n) := by
  let O (m : ℕ) : ℚ := m / 2 ^ m
  let S (m : ℕ) := ∑ k ∈ Finset.range (m + 1), (Nat.fib k : ℚ) * O (m - k)
  have shift (m : ℕ) :
      S (m + 1) = ∑ k ∈ Finset.range (m + 1), (Nat.fib (k + 1) : ℚ) * O (m - k) := by
    dsimp only [S]
    rw [Finset.sum_range_succ']
    simp
  have step (m : ℕ) : S (m + 2) = S m + S (m + 1) + O (m + 1) := by
    rw [shift (m + 1), Finset.sum_range_succ', shift m]
    simp [S, Nat.fib_add_two, add_mul, Finset.sum_add_distrib]
  change S n = _
  induction n using Nat.twoStepInduction with
  | zero => norm_num [S, O]
  | one => norm_num [S, O, Finset.sum_range_succ]
  | more n ih₀ ih₁ =>
    rw [step, ih₀, ih₁, Nat.fib_add_two (n := n + 1)]
    simp only [O, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    field_simp
    ring

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

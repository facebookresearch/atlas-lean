/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tribonacci numbers from every third term of A077943

The terms of A077943 at positive multiples of three are Tribonacci numbers scaled by powers of two.
-/

namespace MetaMathlibExt

/-- **Tribonacci numbers from every third term of A077943.** Let $T_n$ be the Tribonacci
numbers, $T_0 = T_1 = 0$, $T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$. Let
$(y_n)_{n \ge 0}$ be a sequence of integers with $y_0 = y_1 = 0$, $y_2 = 1$ and
$y_{n+3} = 2y_{n+2} - 2y_{n+1} + 2y_n$ for all $n \ge 0$ (the sequence A077943). Then for
every $n \ge 0$, $2^{n+1} T_{n+2} = y_{3(n+1)}$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 27 (`jis-2025-25.3.5-thm-27`). -/
public theorem two_pow_mul_tribonacci_eq (y : ℕ → ℤ) (hy0 : y 0 = 0) (hy1 : y 1 = 0)
    (hy2 : y 2 = 1) (hy : ∀ n, y (n + 3) = 2 * y (n + 2) - 2 * y (n + 1) + 2 * y n) (n : ℕ) :
    2 ^ (n + 1) * (tribonacci (n + 2) : ℤ) = y (3 * (n + 1)) := by
  -- Eliminate the intermediate terms of the recurrence for y.
  have stride (m : ℕ) : y (3 * (m + 3)) =
      2 * y (3 * (m + 2)) + 4 * y (3 * (m + 1)) + 8 * y (3 * m) := by
    simp only [Nat.mul_add, Nat.reduceMul, Nat.mul_one]
    generalize 3 * m = k
    linear_combination hy (k + 6) + 2 * hy (k + 5) + 2 * hy (k + 4) + 4 * hy (k + 1) + 4 * hy k
  induction n using tribonacci.induct with
  | case1 =>
    change (2 : ℤ) = y 3
    norm_num [hy 0, hy0, hy1, hy2]
  | case2 =>
    change (4 : ℤ) = y 6
    norm_num [hy 3, hy 2, hy 1, hy 0, hy0, hy1, hy2]
  | case3 =>
    change (16 : ℤ) = y 9
    norm_num [stride 0, hy 3, hy 2, hy 1, hy 0, hy0, hy1, hy2]
  | case4 n ih₂ ih₁ ih₀ =>
    rw [stride (n + 1), ← ih₂, ← ih₁, ← ih₀, tribonacci.eq_4 (n + 2)]
    simp only [Nat.succ_eq_add_one, Int.natCast_add, pow_succ]
    ring

end MetaMathlibExt

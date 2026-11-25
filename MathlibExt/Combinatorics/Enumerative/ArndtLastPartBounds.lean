/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ArndtLastPart
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Arndt compositions with bounded last part

The counts with last part at most or at least a given threshold are obtained by telescoping
the contributions of terminal singletons and descending pairs.
-/

namespace MetaMathlibExt

namespace arndtLastPart_atMost_atLeast

-- The singleton contribution to the tail includes the composition [n] at j = n.
private def tail (n j : ℕ) : ℕ :=
  (if n = j then 1 else Nat.fib (n - j)) + Nat.fib (n - 2 * j)

private lemma singleton_step (d : ℕ) :
    (if d = 0 then 1 else Nat.fib (d - 2)) + (if d = 1 then 1 else Nat.fib (d - 1)) =
      (if d = 0 then 1 else Nat.fib d) := by
  match d with
  | 0 | 1 => decide
  | d + 2 => simp [Nat.fib_add_two (n := d)]

private lemma pair_step (d : ℕ) :
    (if d = 1 then 1 else Nat.fib (d - 1)) + Nat.fib (d - 2) = Nat.fib d := by
  match d with
  | 0 | 1 => decide
  | d + 2 => simp [Nat.fib_add_two (n := d), add_comm]

private lemma count_add_tail {n j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    arndtLastPartCount n j + tail n (j + 1) = tail n j := by
  rw [count_by_terminal_block hj hjn]
  simp only [tail, show n = j ↔ n - j = 0 by omega, show n = j + 1 ↔ n - j = 1 by omega,
    show n = 2 * j + 1 ↔ n - 2 * j = 1 by omega, show n - (j + 1) = n - j - 1 by omega,
    show n - 2 * (j + 1) = n - 2 * j - 2 by omega]
  have := singleton_step (n - j)
  have := pair_step (n - 2 * j)
  omega

private lemma sum_add_tail {n a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ n) :
    (∑ j ∈ Finset.Icc a b, arndtLastPartCount n j) + tail n (b + 1) = tail n a := by
  induction b, hab using Nat.le_induction with
  | base => simpa using count_add_tail ha hb
  | succ b hab ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_assoc, count_add_tail (by omega) hb]
    exact ih (by omega)

end arndtLastPart_atMost_atLeast

open arndtLastPart_atMost_atLeast in
/-- **Arndt compositions with last part at most or at least $k$.** Let $F_n$ be the $n$-th
Fibonacci number ($F_0 = 0$, $F_1 = 1$) and $b(n, j)$ the number of Arndt compositions of $n$
with last part $j$. For all integers $k \ge 1$ and $n \ge 2k + 2$, the number of Arndt
compositions of $n$ with last part at most $k$ is
$\sum_{j=1}^{k} b(n, j) = F_n - F_{n-k-1} - F_{n-2k-2}$, and the number with last part at least
$k$ is $\sum_{j=k}^{n} b(n, j) = F_{n-k} + F_{n-2k}$.

The paper prints the second count as $F_{n-k} - F_{n-2k}$, which is false: for $k = 1$ and
$n = 4$ all $F_4 = 3$ Arndt compositions of $4$ have last part at least $1$, while
$F_3 - F_2 = 1$. The sign $+$ is the one the paper's own consequence uses ($F_{n-2} + F_{n-4}$
compositions with last part greater than $1$), and it is what subtracting the number with last
part at most $k - 1$ from $F_n$ gives.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 4 (`integers-2024-A35-cor-4`). -/
public theorem arndtLastPart_atMost_atLeast (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k + 2 ≤ n) :
    ((∑ j ∈ Finset.Icc 1 k, arndtLastPartCount n j : ℕ) : ℤ) =
        Nat.fib n - Nat.fib (n - k - 1) - Nat.fib (n - 2 * k - 2) ∧
      ∑ j ∈ Finset.Icc k n, arndtLastPartCount n j = Nat.fib (n - k) + Nat.fib (n - 2 * k) := by
  have lower := sum_add_tail (n := n) (by decide : 1 ≤ 1) hk (show k ≤ n by omega)
  have upper := sum_add_tail hk (show k ≤ n by omega) le_rfl
  have total := Nat.fib_add_two (n := n - 2)
  rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at total
  simp [tail, show n ≠ k + 1 by omega, show n ≠ 1 by omega, show n ≠ k by omega,
    show n - (2 * n + 2) = 0 by omega, Nat.mul_add] at lower upper
  simp only [Nat.sub_sub]
  constructor <;> omega

end MetaMathlibExt

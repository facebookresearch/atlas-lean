/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Alternating sums of Fibonacci numbers

The alternating Fibonacci sums satisfy a first-order recurrence and are tempered from index 12.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Alternating sums of Fibonacci numbers.** Let $F_k$ denote the $k$-th Fibonacci number,
with $F_0 = 0$ and $F_1 = 1$. For a natural number $n$, the $n$-th alternating Fibonacci sum is
the integer
$$W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k.$$
The sequence begins $0, 1, 0, 2, 1, 4, 4, 9, \dots$

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (9). -/
public def fibonacciAlternatingSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (Nat.fib k : ℤ)

/-- **The alternating Fibonacci sum at 0.** Let $F_k$ denote the $k$-th Fibonacci number, with
$F_0 = 0$ and $F_1 = 1$, and let $W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k$. Then $W_0 = 0$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 3. -/
public theorem fibonacciAlternatingSum_zero : fibonacciAlternatingSum 0 = 0 := by
  simp [fibonacciAlternatingSum]

/-- **Recurrence for alternating Fibonacci sums.** Let $F_k$ denote the $k$-th Fibonacci
number, with $F_0 = 0$ and $F_1 = 1$, and let $W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k$. For every
natural number $n$, $W_{n+1} = F_{n+1} - W_n$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (9). -/
public theorem fibonacciAlternatingSum_succ (n : ℕ) :
    fibonacciAlternatingSum (n + 1) = Nat.fib (n + 1) - fibonacciAlternatingSum n := by
  rw [fibonacciAlternatingSum, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul,
    fibonacciAlternatingSum, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

namespace fibonacciAlternatingSum_tempered

private lemma closed_form (k : ℕ) :
    fibonacciAlternatingSum (k + 1) = (Nat.fib k : ℤ) + (-1) ^ k := by
  induction k with
  | zero => simp [fibonacciAlternatingSum_succ, fibonacciAlternatingSum_zero]
  | succ k ih =>
    rw [fibonacciAlternatingSum_succ, ih, Nat.fib_add_two, Nat.cast_add, pow_succ]
    ring

-- Cassini's identity cancels the quadratic terms in the difference of products.
private lemma product_error (k : ℕ) :
    |fibonacciAlternatingSum (k + 1) * fibonacciAlternatingSum (k + 3) -
        fibonacciAlternatingSum (k + 2) ^ 2| ≤ 5 * (Nat.fib (k + 1) : ℤ) := by
  have hc := Int.fib_succ_mul_fib_pred_sub_fib_sq ((k + 1 : ℕ) : ℤ)
  rw [show ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) by omega,
    show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega] at hc
  simp only [Int.fib_natCast, Int.natAbs_natCast, pow_succ (-1 : ℤ), mul_neg_one] at hc
  have hdiff : fibonacciAlternatingSum (k + 1) * fibonacciAlternatingSum (k + 3) -
      fibonacciAlternatingSum (k + 2) ^ 2 =
      (-1 : ℤ) ^ k * (Nat.fib k + 2 * (Nat.fib (k + 1) : ℤ) + Nat.fib (k + 2) - 1) := by
    rw [closed_form k, closed_form (k + 2), closed_form (k + 1),
      pow_succ (-1 : ℤ) (k + 1), pow_succ (-1 : ℤ) k]
    linear_combination hc
  rw [hdiff, abs_mul, abs_neg_one_pow, one_mul, abs_le]
  have hm := @Nat.fib_le_fib_succ k
  rw [Nat.fib_add_two, Nat.cast_add]
  have hp : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
  omega

-- From k = 10 on, each Fibonacci increment is at least five.
private lemma linear_growth (k : ℕ) (hk : 10 ≤ k) :
    5 * (k + 3) + 2 ≤ Nat.fib (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h := Nat.fib_mono (show 5 ≤ k by omega)
    rw [show Nat.fib 5 = 5 by decide] at h
    rw [Nat.fib_add_two]
    omega

end fibonacciAlternatingSum_tempered

open fibonacciAlternatingSum_tempered

/-- **The alternating Fibonacci sums are eventually tempered.** Let $F_k$ denote the $k$-th
Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, and let $W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k$.
For every natural number $n \ge 12$,
$$n W_n^2 \le (n+1) W_{n-1} W_{n+1} \quad\text{and}\quad n W_{n-1} W_{n+1} \le (n+1) W_n^2.$$

These are the conditions $\frac{n}{n+1} x_{n-1} \le x_n \le \frac{n+1}{n} x_{n-1}$ on the
quotients $x_n = W_{n+1}/W_n$, cleared of denominators (all terms are positive here), so the
sequence $(W_n)_{n \ge 11}$ is tempered, with the conditions imposed at every index $n \ge 12$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 4. -/
public theorem fibonacciAlternatingSum_tempered (n : ℕ) (hn : 12 ≤ n) :
    n * fibonacciAlternatingSum n ^ 2 ≤
        (n + 1) * (fibonacciAlternatingSum (n - 1) * fibonacciAlternatingSum (n + 1)) ∧
      n * (fibonacciAlternatingSum (n - 1) * fibonacciAlternatingSum (n + 1)) ≤
        (n + 1) * fibonacciAlternatingSum n ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  push_cast
  have hg : 5 * ((k : ℤ) + 3) + 2 ≤ Nat.fib (k + 1) := by
    exact_mod_cast linear_growth k (by omega)
  have hm : (Nat.fib (k + 1) : ℤ) - 1 ≤ fibonacciAlternatingSum (k + 2) := by
    rw [closed_form (k + 1), pow_succ]
    rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> omega
  have hscale : ((k : ℤ) + 3) * (5 * Nat.fib (k + 1)) ≤
      fibonacciAlternatingSum (k + 2) ^ 2 := calc
    _ ≤ ((Nat.fib (k + 1) : ℤ) - 1) ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hg (Int.natCast_nonneg (Nat.fib (k + 1)))]
    _ ≤ _ := pow_le_pow_left₀ (by omega) hm 2
  obtain ⟨hl, hu⟩ := abs_le.mp (product_error k)
  constructor
  · linarith only [hscale, mul_le_mul_of_nonneg_left hl (show 0 ≤ (k : ℤ) + 3 by omega)]
  · linarith only [hscale, mul_le_mul_of_nonneg_left hu (show 0 ≤ (k : ℤ) + 2 by omega),
      Int.natCast_nonneg (Nat.fib (k + 1))]

end

end MetaMathlibExt

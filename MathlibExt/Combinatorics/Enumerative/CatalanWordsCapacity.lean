/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Fib.Basic

namespace MetaMathlibExt

open Finset

namespace fib_two_mul_eq_sum_sum_choose_mul_fib_odd

private theorem sum_pow_mul_fib (k : ℕ) :
    ∑ m ∈ range (k + 1), 2 ^ (k - m) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) =
      Nat.fib (2 * k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    -- Every old term doubles, and the new term contributes the next odd Fibonacci number.
    have hpow (m : ℕ) (hm : m ∈ range (k + 1)) :
        2 ^ (k + 1 - m) = 2 * 2 ^ (k - m) := by
      rw [mem_range] at hm
      rw [show k + 1 - m = k - m + 1 by omega, pow_succ']
    rw [sum_congr rfl (fun m hm =>
      congrArg (· * (if m = 0 then 1 else Nat.fib (2 * m - 1))) (hpow m hm))]
    simp_rw [mul_assoc]
    rw [← mul_sum, ih]
    simp only [Nat.sub_self, pow_zero, one_mul, Nat.succ_ne_zero, ite_false]
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by omega,
      Nat.fib_add_two (n := 2 * k + 2), Nat.fib_add_two (n := 2 * k + 1),
      show 2 * k + 1 + 1 = 2 * k + 2 by omega]
    omega

end fib_two_mul_eq_sum_sum_choose_mul_fib_odd

/-- **A double-sum identity for even-indexed Fibonacci numbers.** Let $F_k$ be the Fibonacci
numbers, with $F_0 = 0$, $F_1 = 1$ and $F_{k+2} = F_{k+1} + F_k$, and set $F_{-1} = 1$. For every
natural number $n \ge 1$,
$$F_{2n} = \sum_{j=1}^{n} \sum_{m=0}^{n-j} \binom{n-m-1}{j-1} F_{2m-1}.$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 5 (`integers-2025-A5-lem-5`). -/
public theorem fib_two_mul_eq_sum_sum_choose_mul_fib_odd (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * n) =
      ∑ j ∈ Finset.Icc 1 n, ∑ m ∈ Finset.range (n - j + 1),
        (n - m - 1).choose (j - 1) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- Fixing m first leaves the complete binomial row with upper index k - m.
  rw [sum_comm' (t' := range (k + 1)) (s' := fun m => Ico 1 (k - m + 2)) (fun j m => by
    simp only [mem_Icc, mem_range, mem_Ico]
    omega)]
  rw [show 2 * (k + 1) = 2 * k + 2 by omega,
    ← fib_two_mul_eq_sum_sum_choose_mul_fib_odd.sum_pow_mul_fib]
  apply sum_congr rfl
  intro m hm
  rw [← sum_mul, sum_Ico_eq_sum_range]
  simp only [mem_range] at hm
  rw [show k + 1 - m - 1 = k - m by omega]
  simp [Nat.sum_range_choose]

end MetaMathlibExt

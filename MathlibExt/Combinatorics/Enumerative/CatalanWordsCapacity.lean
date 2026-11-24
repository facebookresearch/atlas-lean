/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci sums for Catalan word capacity

The two identities express even Fibonacci numbers and binomial sums of odd Fibonacci numbers
as double sums of binomially weighted odd Fibonacci numbers.
-/

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

namespace sum_choose_mul_fib_odd_eq_choose_add_sum

private theorem fib_odd_split (m : ℕ) :
    Nat.fib (2 * m + 1) = (if m = 0 then 1 else Nat.fib (2 * m - 1)) +
      ∑ r ∈ range m, Nat.fib (2 * r + 1) := by
  have h (k : ℕ) : ∑ r ∈ range k, Nat.fib (2 * r + 1) = Nat.fib (2 * k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ih, show 2 * (k + 1) = 2 * k + 2 by omega, Nat.fib_add_two]
  rw [h]
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ite_false]
    rw [show 2 * (m + 1) + 1 = (2 * (m + 1) - 1) + 2 by omega,
      Nat.fib_add_two, show 2 * (m + 1) - 1 + 1 = 2 * (m + 1) by omega]

private theorem sum_rows (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n + 1) :
    (∑ m ∈ range (n + 1 - i), (n - m - 2).choose (i - 2) * Nat.fib (2 * m + 1)) =
      ∑ j ∈ Icc i n, ∑ m ∈ range (n - j + 1),
        (n - m - 2).choose (j - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) := by
  induction hd : n + 1 - i generalizing i with
  | zero =>
    simp [Icc_eq_empty_of_lt (show n < i by omega)]
  | succ d ih =>
    have hi' : i ≤ n := by omega
    rw [← insert_Icc_succ_left_eq_Icc hi', sum_insert (by simp), Nat.succ_eq_succ,
      ← ih (i + 1) (by omega) (by omega) (by omega)]
    have : d = n - i := by omega
    subst d
    -- Splitting each Fibonacci weight gives the row at i and a triangular sum.
    conv_lhs => enter [2, m, 2]; rw [fib_odd_split m]
    simp_rw [mul_add, sum_add_distrib, mul_sum]
    congr 1
    -- Reverse the triangular sum and sum each column by the hockey-stick identity.
    rw [sum_comm' (t' := range (n - i)) (s' := fun r => Ico (r + 1) (n - i + 1))
      (fun m r => by simp only [mem_range, mem_Ico]; omega)]
    refine sum_congr rfl fun r hr => ?_
    have hr' := mem_range.mp hr
    rw [← sum_mul]
    congr 1
    simp_rw [show ∀ m, n - m - 2 = n - 2 - m by omega]
    rw [sum_Ico_reflect (fun t => t.choose (i - 2)) _ (by omega),
      show n - 2 + 1 - (n - i + 1) = i - 2 by omega,
      show n - 2 + 1 - (r + 1) = (n - 2 - r - 1) + 1 by omega,
      Ico_add_one_right_eq_Icc, Nat.sum_Icc_choose,
      show n - 2 - r - 1 + 1 = n - 2 - r by omega,
      show i + 1 - 2 = i - 2 + 1 by omega]

end sum_choose_mul_fib_odd_eq_choose_add_sum

set_option linter.unusedVariables false in
/-- **A recursion for binomial sums of odd-indexed Fibonacci numbers.** Let $F_k$ be the Fibonacci
numbers, with the convention $F_{-1} = 1$. For all integers $n \ge 1$ and $2 \le i \le n + 1$,
$$\sum_{m=0}^{n-i+1} \binom{n-m-1}{i-2} F_{2m-1} =
\binom{n-1}{i-2} + \sum_{j=i}^{n} \sum_{m=0}^{n-j} \binom{n-m-2}{j-2} F_{2m-1}$$
(Mansour and Shattuck's Lemma 5, identity (21)). All differences in the binomial coefficients and
in the summation bounds are nonnegative.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 5 (`integers-2025-A5-lem-5`). -/
public theorem sum_choose_mul_fib_odd_eq_choose_add_sum (n i : ℕ) (hn : 1 ≤ n)
    (hi : 2 ≤ i) (hin : i ≤ n + 1) :
    ∑ m ∈ Finset.range (n + 2 - i),
        (n - m - 1).choose (i - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) =
      (n - 1).choose (i - 2) +
        ∑ j ∈ Finset.Icc i n, ∑ m ∈ Finset.range (n - j + 1),
          (n - m - 2).choose (j - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) := by
  rw [show n + 2 - i = (n + 1 - i) + 1 by omega, sum_range_succ']
  simp only [Nat.sub_zero, ite_true, mul_one, Nat.succ_ne_zero, ite_false]
  rw [add_comm, ← sum_choose_mul_fib_odd_eq_choose_add_sum.sum_rows n i hi hin]
  congr 1

end MetaMathlibExt

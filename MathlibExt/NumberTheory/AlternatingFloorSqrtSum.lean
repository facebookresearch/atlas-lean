/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.Ring

/-!
# An alternating sum of floors of square roots

For odd positive `n`, the alternating sum of the integer square roots of `j * n` for
`1 ≤ j ≤ n` is `(n + 1) / 2`, as stated by Marc Chamberland and Karl Dilcher in
"An Alternating Sum of the Floor Function of Square Roots"
([arXiv:2510.26291](https://arxiv.org/abs/2510.26291)).

The proof counts the positive integers `k` with `k ^ 2 ≤ j * n` and exchanges the
two sums. Each `k` contributes the parity of the ceiling of `k ^ 2 / n`.
The reflection `k ↦ n - k` pairs each odd ceiling with an even one.
-/

set_option autoImplicit false

@[expose] public section

open Finset

namespace MathlibExt.NumberTheory.AlternatingFloorSqrtSumWanted

-- The alternating sum from a threshold to the odd endpoint telescopes to its parity.
private theorem alternating_tail {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n) (hodd : Odd n) :
    (∑ j ∈ Icc 1 n, if a ≤ j then (-1 : ℤ) ^ (j + 1) else 0) = ↑(a % 2) := by
  have hfilter : (Icc 1 n).filter (a ≤ ·) = Ico a (n + 1) := by
    ext j
    simp only [mem_filter, mem_Icc, mem_Ico]
    omega
  have hstep (j : ℕ) : (-1 : ℤ) ^ (j + 1) =
      -(↑((j + 1) % 2) : ℤ) - -(↑(j % 2) : ℤ) := by
    simp only [neg_one_pow_eq_ite, Nat.even_iff]
    split <;> omega
  rw [← sum_filter, hfilter]
  simp_rw [hstep]
  rw [sum_Ico_sub (fun i ↦ -(↑(i % 2) : ℤ)) (by omega)]
  have := Nat.odd_iff.mp hodd
  omega

-- Expand each integer square root as a count of columns.
private theorem sqrt_eq_sum {j n : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (Nat.sqrt (j * n) : ℤ) =
      ∑ k ∈ Icc 1 n, if k ^ 2 ⌈/⌉ n ≤ j then (1 : ℤ) else 0 := by
  have hsqrt : Nat.sqrt (j * n) ≤ n := by
    simpa using Nat.sqrt_le_sqrt (Nat.mul_le_mul_right n hj)
  have hfilter : (Icc 1 n).filter (fun k ↦ k ^ 2 ⌈/⌉ n ≤ j) = Icc 1 (Nat.sqrt (j * n)) := by
    ext k
    simp only [mem_filter, mem_Icc, ceilDiv_le_iff_le_mul hn, mul_comm n j, ← Nat.le_sqrt']
    omega
  rw [sum_boole, hfilter, Nat.card_Icc]
  simp

-- The two ceiling quotients differ by n - 2k as integers, hence have opposite parity.
private theorem reflected_parity {k n : ℕ} (hn : 0 < n) (hodd : Odd n) (hk : k ≤ n) :
    (k ^ 2 ⌈/⌉ n) % 2 + ((n - k) ^ 2 ⌈/⌉ n) % 2 = 1 := by
  have hsq : (n - k) ^ 2 + 2 * k * n = k ^ 2 + n * n := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp only [Nat.add_sub_cancel_left]
    ring
  have hnum : ((n - k) ^ 2 + (n - 1)) + 2 * k * n = (k ^ 2 + (n - 1)) + n * n := by
    omega
  have hdiv := congrArg (· / n) hnum
  rw [Nat.add_mul_div_right _ _ hn, Nat.add_mul_div_right _ _ hn] at hdiv
  simp only [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hn]
  have parity (a b : ℕ) (h : b + 2 * k = a + n) : a % 2 + b % 2 = 1 := by
    have := Nat.odd_iff.mp hodd
    omega
  exact parity _ _ hdiv

private theorem sum_parities {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    (∑ k ∈ Icc 1 n, (↑((k ^ 2 ⌈/⌉ n) % 2) : ℤ)) = ↑((n + 1) / 2) := by
  let f (k : ℕ) : ℤ := ↑((k ^ 2 ⌈/⌉ n) % 2)
  have hpair (k : ℕ) (hk : k ∈ range (n + 1)) : f k + f (n - k) = 1 := by
    dsimp only [f]
    exact_mod_cast reflected_parity hn hodd (Nat.le_of_lt_succ (mem_range.mp hk))
  have hreflect : ∑ k ∈ range (n + 1), f (n - k) = ∑ k ∈ range (n + 1), f k := by
    simpa using sum_range_reflect f (n + 1)
  have hsum : (∑ k ∈ range (n + 1), f k) + (∑ k ∈ range (n + 1), f k) = ↑(n + 1) := by
    calc
      _ = ∑ k ∈ range (n + 1), (f k + f (n - k)) := by rw [sum_add_distrib, hreflect]
      _ = ∑ _k ∈ range (n + 1), (1 : ℤ) := sum_congr rfl hpair
      _ = _ := by simp
  rw [sum_range_eq_add_Ico f (show 0 < n + 1 by omega), Ico_add_one_right_eq_Icc] at hsum
  have hzero : f 0 = 0 := by simp [f]
  change ∑ k ∈ Icc 1 n, f k = _
  omega

/-- **An alternating sum of floors of square roots.** For every odd positive integer $n$,
$\sum_{j=1}^{n} (-1)^{j+1} \lfloor \sqrt{jn} \rfloor = (n+1)/2$.

Source: Marc Chamberland and Karl Dilcher, "An Alternating Sum of the
Floor Function of Square Roots", Theorem 1 (TeX label `thm:7.1`). -/
theorem alternating_sum_floor_sqrt_mul
    {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) :
    (∑ j ∈ Finset.Icc 1 n,
      (-1 : ℤ) ^ (j + 1) * (Nat.sqrt (j * n) : ℤ)) =
      (((n + 1) / 2 : ℕ) : ℤ) := by
  calc
    _ = ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n,
          if k ^ 2 ⌈/⌉ n ≤ j then (-1 : ℤ) ^ (j + 1) else 0 := by
      refine sum_congr rfl fun j hj ↦ ?_
      rw [sqrt_eq_sum hn (mem_Icc.mp hj).2, mul_sum]
      simp [mul_ite]
    _ = ∑ k ∈ Icc 1 n, (↑((k ^ 2 ⌈/⌉ n) % 2) : ℤ) := by
      rw [sum_comm]
      refine sum_congr rfl fun k hk ↦ alternating_tail ?_ ?_ hodd
      · change 0 < k ^ 2 ⌈/⌉ n
        apply (gc_mul_ceilDiv (show 0 < n from hn)).lt_iff_lt.mpr
        simpa using pow_pos (show 0 < k from (mem_Icc.mp hk).1) 2
      · exact (ceilDiv_le_iff_le_mul hn).mpr (by
          simpa [pow_two] using Nat.mul_self_le_mul_self (mem_Icc.mp hk).2)
    _ = _ := sum_parities hn hodd

end MathlibExt.NumberTheory.AlternatingFloorSqrtSumWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.KnuthOldSum
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Choose.Sum

/-!
# Tefera–Zeleke identity with powers of 2, 3 and 4

A binomial transform proved by Pascal's recurrence gives the power-sum formula
for Knuth's old sum.
-/

namespace MathlibExt.Combinatorics.KnuthOldSumWanted

open Finset

-- Pascal's recurrence for the coefficients gives a recurrence for the weighted sums.
private theorem sum_pascal (a b : ℚ) (n : ℕ) (f g h : ℕ → ℚ)
    (hzero : f 0 = h 0) (hsucc : ∀ k, f (k + 1) = g k + h (k + 1)) :
    (∑ k ∈ range (n + 2), f k * a ^ k * b ^ (n + 1 - k)) =
      a * (∑ k ∈ range (n + 1), g k * a ^ k * b ^ (n - k)) +
        ∑ k ∈ range (n + 2), h k * a ^ k * b ^ (n + 1 - k) := by
  rw [sum_range_succ' (fun k => f k * a ^ k * b ^ (n + 1 - k)) (n + 1),
    sum_range_succ' (fun k => h k * a ^ k * b ^ (n + 1 - k)) (n + 1), mul_sum]
  simp only [hsucc, hzero, Nat.add_sub_add_right, add_mul]
  rw [sum_add_distrib, add_assoc]
  congr 1
  exact sum_congr rfl fun k _ => by rw [pow_succ]; ring

-- The two sums obey the same recurrence in the degree and the excess of the upper index.
private theorem sum_choose_eq_sum_multichoose (a : ℚ) (n r : ℕ) :
    (∑ k ∈ range (n + 1),
      ((n + r).choose k : ℚ) * a ^ k * (-1 : ℚ) ^ (n - k)) =
      ∑ k ∈ range (n + 1), (r.multichoose k : ℚ) * a ^ k * (a - 1) ^ (n - k) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    induction r with
    | zero =>
      calc
        _ = (a + -1) ^ (n + 1) := by
          rw [add_pow, Nat.add_zero]
          exact sum_congr rfl fun k _ => by ring
        _ = _ := by
          rw [sum_range_succ']
          simp [sub_eq_add_neg]
    | succ r ihr =>
      have hchoose := sum_pascal a (-1) n
        (fun k => ((n + 1 + (r + 1)).choose k : ℚ))
        (fun k => ((n + (r + 1)).choose k : ℚ)) (fun k => ((n + 1 + r).choose k : ℚ))
        (by simp) (fun k => by
          rw [show n + 1 + (r + 1) = n + (r + 1) + 1 by omega,
            Nat.choose_succ_succ', Nat.cast_add, show n + 1 + r = n + (r + 1) by omega])
      have hmultichoose := sum_pascal a (a - 1) n
        (fun k => ((r + 1).multichoose k : ℚ))
        (fun k => ((r + 1).multichoose k : ℚ)) (fun k => (r.multichoose k : ℚ))
        (by simp) (fun k => by
          rw [Nat.multichoose_succ_succ, Nat.cast_add, add_comm])
      rw [hchoose, hmultichoose, ih (r + 1), ihr]

/-- **Tefera–Zeleke identity with powers of $2$, $3$ and $4$.** Let $n$ and $j$ be natural numbers,
let $N = n + 2j + 1$, and let $w(m) = (4^m + 2^m)/2$ be the weight in Knuth's old sum. Then, in the
rational numbers,
$$\sum_{k=0}^{n} \binom{N}{n-k} w(n-k) (-1)^k
= \sum_{k=0}^{n} \binom{2j+k}{k} \frac{2^k + 4^k 3^{n-k}}{2}.$$

This is Equation (2) of the paper, which prints the weight as $(2^m + 1) 2^{m-1}$ and the terms
on the right as $\binom{2j+k}{k} 2^{k-1} (1 + 2^k 3^{n-k})$.

Source: Akalu Tefera and Aklilu Zeleke, "Combinatorial Identities
Inspired by Knuth's Old Sum", Theorem 2. -/
public theorem knuthOldSum_eq_sum_pow (n j : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose (n + 2 * j + 1) (n - k) : ℚ) *
        knuthOldSumWeight (n - k) * (-1 : ℚ) ^ k) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * j + k) k : ℚ) *
          (((2 : ℚ) ^ k + (4 : ℚ) ^ k * (3 : ℚ) ^ (n - k)) / 2) := by
  have hpow (a : ℚ) :
      (∑ k ∈ range (n + 1), ((n + 2 * j + 1).choose (n - k) : ℚ) *
        a ^ (n - k) * (-1 : ℚ) ^ k) =
        ∑ k ∈ range (n + 1), ((2 * j + k).choose k : ℚ) * a ^ k * (a - 1) ^ (n - k) := by
    calc
      _ = ∑ k ∈ range (n + 1), ((n + 2 * j + 1).choose k : ℚ) *
          a ^ k * (-1 : ℚ) ^ (n - k) := by
        rw [← sum_range_reflect (fun k => ((n + 2 * j + 1).choose k : ℚ) *
          a ^ k * (-1 : ℚ) ^ (n - k)) (n + 1)]
        simp only [Nat.add_sub_cancel]
        exact sum_congr rfl fun k hk => by
          rw [Nat.sub_sub_self (Nat.le_of_lt_succ (mem_range.mp hk))]
      _ = _ := by
        rw [show n + 2 * j + 1 = n + (2 * j + 1) by omega, sum_choose_eq_sum_multichoose]
        exact sum_congr rfl fun k _ => by
          rw [Nat.multichoose_eq, show 2 * j + 1 + k - 1 = 2 * j + k by omega]
  have hfour := hpow 4
  have htwo := hpow 2
  rw [show (4 : ℚ) - 1 = 3 by norm_num] at hfour
  rw [show (2 : ℚ) - 1 = 1 by norm_num] at htwo
  simp only [one_pow, mul_one] at htwo
  have hsplit (c x y s : ℚ) : c * ((x + y) / 2) * s = (c * x * s + c * y * s) / 2 := by
    ring
  simp only [knuthOldSumWeight, hsplit]
  simp only [← mul_div_assoc, mul_add]
  simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib]
  rw [hfour, htwo, add_comm]
  simp only [mul_assoc]

end MathlibExt.Combinatorics.KnuthOldSumWanted

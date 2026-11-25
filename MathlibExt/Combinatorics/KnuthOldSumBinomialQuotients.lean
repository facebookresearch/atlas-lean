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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Rat

/-!
# Tefera–Zeleke identity with binomial quotients

The binomial product identity gives the quotient formula for each coefficient of Knuth's old sum.
-/

namespace MathlibExt.Combinatorics.KnuthOldSumWanted

/-- **Tefera–Zeleke identity with binomial quotients.** Let $n$ and $j$ be natural numbers, let
$N = n + 2j + 1$, and let $w(m) = (4^m + 2^m)/2$ be the weight in Knuth's old sum. Then, in the
rational numbers,
$$\sum_{k=0}^{n} \binom{N}{n-k} w(n-k) (-1)^k
= \binom{N}{n} \sum_{k=0}^{n} \frac{\binom{n}{k}}{\binom{2j+1+k}{2j+1}} w(n-k) (-1)^k.$$

This is Equation (1) of the paper, whose weight $(2^m + 1) 2^{m-1}$ is written here as
$(4^m + 2^m)/2$.

Source: Akalu Tefera and Aklilu Zeleke, "Combinatorial Identities
Inspired by Knuth's Old Sum", Theorem 1. -/
public theorem knuthOldSum_eq_mul_sum_div (n j : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose (n + 2 * j + 1) (n - k) : ℚ) *
        knuthOldSumWeight (n - k) * (-1 : ℚ) ^ k) =
      (Nat.choose (n + 2 * j + 1) n : ℚ) *
        ∑ k ∈ Finset.range (n + 1),
          ((Nat.choose n k : ℚ) /
            (Nat.choose (2 * j + 1 + k) (2 * j + 1) : ℚ)) *
            knuthOldSumWeight (n - k) * (-1 : ℚ) ^ k := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have h := Nat.choose_mul (n := n + 2 * j + 1) (Nat.sub_le n k)
  rw [Nat.choose_symm hkn, show n + 2 * j + 1 - (n - k) = 2 * j + 1 + k by omega,
    Nat.sub_sub_self hkn, ← Nat.choose_symm_add] at h
  have hd : ((2 * j + 1 + k).choose (2 * j + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.le_add_right (2 * j + 1) k)
  simp only [← mul_assoc]
  congr 2
  rw [← mul_div_assoc, eq_div_iff hd]
  exact_mod_cast h.symm

end MathlibExt.Combinatorics.KnuthOldSumWanted

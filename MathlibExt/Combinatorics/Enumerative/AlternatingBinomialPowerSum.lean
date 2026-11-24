/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Alternating binomial sums of powers

The alternating sum of order `n` is `(-1)^n` times the `n`-th forward difference
of a power of a linear polynomial at zero.
-/

namespace MetaMathlibExt

open Polynomial
open scoped fwdDiff

/-- **Alternating binomial sums of powers.** Let $x, y, k \in \mathbb{C}$ and let $n, m$ be
positive integers. If $n = m$, then

$$\sum_{i=0}^{n} (-1)^i \binom{n}{i} (kx + iy)^m = (-1)^n y^n n!,$$

and if $m < n$, then $\sum_{i=0}^{n} (-1)^i \binom{n}{i} (kx + iy)^m = 0$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Theorem 3
(`integers-2024-A12-thm-3`). -/
public theorem sum_neg_one_pow_choose_mul_pow (x y k : ℂ) {n m : ℕ} (hn : 0 < n)
    (hm : 0 < m) :
    (n = m → ∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * (n.choose i : ℂ) * (k * x + i * y) ^ m =
          (-1) ^ n * y ^ n * (n.factorial : ℂ)) ∧
      (m < n → ∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * (n.choose i : ℂ) * (k * x + i * y) ^ m = 0) := by
  let P : ℂ[X] := (C y * X + C (k * x)) ^ m
  have hsum : (∑ i ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ i * (n.choose i : ℂ) * (k * x + i * y) ^ m) =
      (-1) ^ n * (Δ_[1]^[n] P.eval) 0 := by
    rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    have hsign : (-1 : ℂ) ^ i = (-1) ^ n * (-1) ^ (n - i) := by
      rw [← pow_add]
      apply neg_one_pow_congr
      simp only [Nat.even_iff]
      omega
    simp only [P, zero_add, nsmul_one, eval_pow, eval_add, eval_mul, eval_X, eval_C,
      zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [hsign]
    ring
  have hzero (h : P.natDegree < n) := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h
  rw [hsum]
  constructor
  · rintro rfl
    by_cases hy : y = 0
    · have hd : P.natDegree < n := by
        simpa only [P, hy, map_zero, zero_mul, zero_add, natDegree_pow, natDegree_C,
          Nat.mul_zero] using hn
      simp [hzero hd, hy, zero_pow hm.ne']
    · have hd : P.natDegree = n := by
        simp only [P, natDegree_pow, natDegree_linear hy, Nat.mul_one]
      have hdiff := congrFun P.fwdDiff_iter_degree_eq_factorial 0
      rw [hd] at hdiff
      rw [hdiff]
      simp only [P, leadingCoeff_pow, leadingCoeff_linear hy, Pi.smul_apply, Pi.natCast_apply,
        smul_eq_mul, mul_assoc]
  · intro hmn
    have hd : P.natDegree ≤ m := by
      simpa only [Nat.mul_one] using natDegree_pow_le_of_le m
        (natDegree_linear_le (a := y) (b := k * x))
    simp [hzero (hd.trans_lt hmn)]

end MetaMathlibExt

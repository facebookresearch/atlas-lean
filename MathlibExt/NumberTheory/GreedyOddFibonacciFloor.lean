/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.NumberTheory.OddFibonacciGoldenRatio

/-!
# Floors of greedy odd-Fibonacci sums

Multiplication by the golden ratio or by one plus the golden ratio shifts the Fibonacci
indices of a greedy sum by one or two places after taking the floor. Both shifts have the
same error, which the greedy prefix inequalities keep strictly below one.
-/

namespace MetaMathlibExt

open Finset

/-- A prefix below the even Fibonacci number has room for one more error term. This
stronger bound is needed when the next digit is two. -/
private lemma greedy_error_lt_one (a : ℕ → ℕ) {q : ℝ} (hq : 0 < q) (hsq : q ^ 2 + q = 1)
    (n : ℕ) (ha : ∀ m ≤ n, ∑ k ∈ range m, a k * Nat.fib (2 * k + 1) < Nat.fib (2 * m + 1)) :
    ∑ k ∈ range n, (a k : ℝ) * q ^ (2 * k + 1) < 1 := by
  let value (m : ℕ) := ∑ k ∈ range m, a k * Nat.fib (2 * k + 1)
  let err (m : ℕ) := ∑ k ∈ range m, (a k : ℝ) * q ^ (2 * k + 1)
  have bounds (m : ℕ) (hm : m ≤ n) :
      err m + q ^ (2 * m) ≤ 1 ∧
        (value m < Nat.fib (2 * m) → err m + q ^ (2 * m) + q ^ (2 * m + 1) ≤ 1) := by
    induction m with
    | zero => simp [err, value]
    | succ m ih =>
      obtain ⟨hbase, hextra⟩ := ih (by omega)
      have heven : Nat.fib (2 * (m + 1)) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.fib_add_two]
      have hodd : Nat.fib (2 * (m + 1) + 1) =
          Nat.fib (2 * m + 1) + Nat.fib (2 * (m + 1)) := by
        simpa only [Nat.mul_add, Nat.mul_one] using Nat.fib_add_two (n := 2 * m + 1)
      have hv : value (m + 1) = value m + a m * Nat.fib (2 * m + 1) := sum_range_succ ..
      have he : err (m + 1) = err m + (a m : ℝ) * q ^ (2 * m + 1) := sum_range_succ ..
      have htotal : value (m + 1) < Nat.fib (2 * (m + 1) + 1) := ha _ hm
      rw [hv, hodd, heven] at htotal
      have hle : Nat.fib (2 * m) ≤ Nat.fib (2 * m + 1) := Nat.fib_le_fib_succ
      have hd : a m ≤ 2 := by
        by_contra! h
        have := Nat.mul_le_mul_right (Nat.fib (2 * m + 1)) h
        omega
      -- The margin lost at this step is exactly the error contributed by a digit of one.
      have hmargin : q ^ (2 * (m + 1)) + q ^ (2 * m + 1) = q ^ (2 * m) := by
        rw [Nat.mul_add, Nat.mul_one, pow_add, pow_succ q (2 * m), ← mul_add, hsq, mul_one]
      have hshrink : q ^ (2 * (m + 1) + 1) ≤ q ^ (2 * m + 1) := by
        apply pow_le_pow_of_le_one hq.le (by nlinarith [sq_nonneg q])
        omega
      rw [he, hv, heven]
      interval_cases h : a m
      · simp only [Nat.cast_zero, zero_mul, add_zero]
        constructor
        · linarith [pow_pos hq (2 * m + 1)]
        · intro _
          linarith
      · simp only [Nat.cast_one, one_mul]
        constructor
        · linarith
        · intro hsmall
          have := hextra (by omega)
          linarith
      · have := hextra (by omega)
        simp only [Nat.cast_ofNat]
        constructor
        · linarith
        · omega
  exact lt_of_lt_of_le (lt_add_of_pos_right _ (pow_pos hq _)) (bounds n le_rfl).1

/-- **Floor of greedy odd-Fibonacci sums times $\varphi$ and $1 + \varphi$.** Let $F_n$ be the
Fibonacci numbers ($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$) and
$\varphi = (1 + \sqrt 5)/2$ the golden ratio. Let $n$ be a natural number and $a_0, a_1, \dots$
natural numbers such that $\sum_{k=0}^{m-1} a_k F_{2k+1} < F_{2m+1}$ for every $m \le n + 1$, and
let $t = \sum_{k=0}^{n} a_k F_{2k+1}$. Then
$\lfloor t \varphi \rfloor = \sum_{k=0}^{n} a_k F_{2k+2}$ and
$\lfloor t (1 + \varphi) \rfloor = \sum_{k=0}^{n} a_k F_{2k+3}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 1
(here $a_k$ is the paper's $a_{2k+1}$); $n$ need not be minimal and $t = 0$ is allowed.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 2. -/
public theorem floor_greedy_odd_fib_sum_mul_goldenRatio (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, a k * Nat.fib (2 * k + 1) < Nat.fib (2 * m + 1)) :
    ⌊((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) : ℕ) : ℝ) * Real.goldenRatio⌋₊ =
        ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 2) ∧
      ⌊((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) : ℕ) : ℝ) * (1 + Real.goldenRatio)⌋₊ =
        ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 3) := by
  let q := (Real.sqrt 5 - 1) / 2
  have hq : 0 < q := by
    have : 1 < Real.sqrt 5 := (Real.lt_sqrt zero_le_one).mpr (by norm_num)
    dsimp [q]
    linarith
  have hsq : q ^ 2 + q = 1 := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  let error := ∑ k ∈ range (n + 1), (a k : ℝ) * q ^ (2 * k + 1)
  have herror : 0 ≤ error := sum_nonneg fun k _ ↦ mul_nonneg (by positivity) (pow_nonneg hq.le _)
  have hlt : error < 1 := greedy_error_lt_one a hq hsq _ ha
  have shift (c : ℝ) (j : ℕ) (hc : ∀ k, (Nat.fib (2 * k + 1) : ℝ) * c =
      Nat.fib (2 * k + j) + q ^ (2 * k + 1)) :
      ⌊((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) : ℕ) : ℝ) * c⌋₊ =
        ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + j) := by
    have hsum : ((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) : ℕ) : ℝ) * c =
        ((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + j) : ℕ) : ℝ) + error := by
      simp only [Nat.cast_sum, Nat.cast_mul, sum_mul, mul_assoc, hc, mul_add, sum_add_distrib,
        error]
    rw [hsum, Nat.floor_eq_iff (by positivity)]
    exact ⟨le_add_of_nonneg_right herror, add_lt_add_right hlt _⟩
  exact ⟨shift _ 2 fun k ↦ (fib_odd_mul_goldenRatio k).1,
    shift _ 3 fun k ↦ (fib_odd_mul_goldenRatio k).2⟩

end MetaMathlibExt

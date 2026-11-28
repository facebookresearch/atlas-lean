/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Generalized Delannoy numbers and parity in Delannoy arrays

The generalized Delannoy numbers with upper index have a power-of-two sum for all natural
numbers `k`, `m` and `n`. The lower-index version requires `k ≤ m` and `k ≤ n`.

## References

- Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal of Integer Sequences
  27 (2024), Article 24.1.8, pp. 1–10, Theorems 9–11
  (<https://cs.uwaterloo.ca/journals/JIS/VOL27/Edwards/ed6.html>). See also Section 1 for the
  definitions and examples, and Sections 3–5 for the other identities and parity results.
- The coefficient argument adapts the expansion in `coeff_delannoyPolynomial_pow` from
  `MathlibExt.NumberTheory.DelannoyBinomialSum` to independent exponents and coefficient degree.
-/

namespace MetaMathlibExt.DelannoyConstructions

open Finset

/-- Expand the triangle entry by Vandermonde and sum over the possible marked subsets. -/
private theorem delannoy_sum_nat (m n : ℕ) :
    ∑ j ∈ range (m + 1), m.choose j * (m + n - j).choose m =
      ∑ k ∈ range (min m n + 1), m.choose k * n.choose k * 2 ^ k := by
  have hsplit (j : ℕ) (hj : j ≤ m) : (m + n - j).choose m =
      ∑ k ∈ range (m + 1), n.choose k * (m - j).choose (m - k) := by
    rw [show m + n - j = n + (m - j) by omega, Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- Choosing j of k marked elements is equivalent to choosing j first and then k - j.
  have hmark (j k : ℕ) (hj : j ≤ m) (hk : k ≤ m) :
      m.choose j * (m - j).choose (m - k) = m.choose k * k.choose j := by
    by_cases hjk : j ≤ k
    · rw [show m - k = (m - j) - (k - j) by omega,
        Nat.choose_symm (show k - j ≤ m - j by omega)]
      exact (Nat.choose_mul hjk).symm
    · simp [Nat.choose_eq_zero_of_lt (show m - j < m - k by omega),
        Nat.choose_eq_zero_of_lt (show k < j by omega)]
  have hbinom (k : ℕ) (hk : k ≤ m) : ∑ j ∈ range (m + 1), k.choose j = 2 ^ k := by
    rw [← Nat.sum_range_choose k]
    symm
    apply sum_subset (range_subset_range.mpr (by omega))
    intro j _ hj
    exact Nat.choose_eq_zero_of_lt (by simpa [mem_range_succ_iff] using hj)
  calc
    _ = ∑ j ∈ range (m + 1), ∑ k ∈ range (m + 1),
        (m.choose k * n.choose k) * k.choose j := by
      apply sum_congr rfl
      intro j hj
      rw [hsplit j (mem_range_succ_iff.mp hj), mul_sum]
      apply sum_congr rfl
      intro k hk
      calc
        _ = (m.choose j * (m - j).choose (m - k)) * n.choose k := by ac_rfl
        _ = _ := by
          rw [hmark j k (mem_range_succ_iff.mp hj) (mem_range_succ_iff.mp hk)]
          ac_rfl
    _ = ∑ k ∈ range (m + 1), (m.choose k * n.choose k) * 2 ^ k := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      rw [← mul_sum, hbinom k (mem_range_succ_iff.mp hk)]
    _ = _ := by
      symm
      apply sum_subset (range_subset_range.mpr (Nat.succ_le_succ (Nat.min_le_left m n)))
      intro k hk hkm
      have hkn : n < k := by
        have hk' := mem_range_succ_iff.mp hk
        have hkm' : ¬ k ≤ min m n := by simpa [mem_range_succ_iff] using hkm
        omega
      simp [Nat.choose_eq_zero_of_lt hkn]

/-- **Delannoy numbers as a sum of powers of two.** For all natural numbers $m$ and $n$, the
Delannoy number $D(m, n)$, that is, the Delannoy triangle entry $T(m + n, m; 1)$, satisfies
$D(m, n) = \sum_{j=0}^{\min(m, n)} \binom{m}{j} \binom{n}{j} 2^j$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 8
(`jis-2024-24.1.8-thm-8`). -/
public theorem delannoy_eq_sum_choose_mul_choose_two_pow (m n : ℕ) :
    ordinaryRiordanPascalLikeMatrix (m + n) m 1 =
      ∑ j ∈ range (min m n + 1), (m.choose j : ℤ) * (n.choose j : ℤ) * 2 ^ j := by
  rw [ordinaryRiordanPascalLikeMatrix_def]
  simp only [one_pow, mul_one]
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    congrArg (fun a : ℕ => (a : ℤ)) (delannoy_sum_nat m n)

/-- **Generalized Delannoy number with upper index.** For natural numbers $k$, $m$ and $n$, the
generalized Delannoy number $D^k(m, n)$ is the natural number

$$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}.$$

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1 (definition of `D^k(m, n)`). -/
@[expose] public def genDelannoyUpper (k m n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), (m + n + k - j).choose (n + k) * n.choose j

/-- **Lower generalized Delannoy number.** For natural numbers $k$, $m$ and $n$, the generalized
Delannoy number $D_k(m, n)$ is
$$D_k(m, n) = \sum_{j=0}^{n} \binom{m + n - k - j}{n - k} \binom{n}{j},$$
where each subtraction is truncated at $0$. The definition is intended for $m, n \ge k$, where
no truncation occurs.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1 (definition of `D_k(m, n)`). -/
@[expose] public def genDelannoyLower (k m n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), (m + n - k - j).choose (n - k) * n.choose j

open Polynomial in
private theorem sum_choose_eq_sum_two_pow (a b n : ℕ) :
    ∑ j ∈ range (n + 1), (a + n - j).choose b * n.choose j =
      ∑ j ∈ Ico (n - b) (min (a + n + 1 - b) (n + 1)),
        a.choose (b - (n - j)) * n.choose j * 2 ^ j := by
  -- Take the same coefficient using two binomial expansions of the second factor.
  calc
    _ = ((X + 1 : ℕ[X]) ^ a * (1 + (X + 1)) ^ n).coeff b := by
      rw [add_pow (1 : ℕ[X]), mul_sum, finsetSum_coeff]
      refine sum_congr rfl fun j hj ↦ ?_
      simp only [one_pow, one_mul, ← mul_assoc, ← pow_add, coeff_mul_natCast,
        coeff_X_add_one_pow, Nat.cast_id]
      rw [show a + n - j = a + (n - j) by have := mem_range.mp hj; omega]
    _ = ((X + 1 : ℕ[X]) ^ a * (2 + X) ^ n).coeff b := by
      have h : (1 + (X + 1) : ℕ[X]) = 2 + X := by
        rw [← one_add_one_eq_two]
        ac_rfl
      rw [h]
    _ = _ := by
      rw [add_pow (2 : ℕ[X]), mul_sum, finsetSum_coeff]
      have hcoeff (j : ℕ) :
          ((X + 1 : ℕ[X]) ^ a * (2 ^ j * X ^ (n - j) * (n.choose j : ℕ[X]))).coeff b =
            if n - j ≤ b then a.choose (b - (n - j)) * n.choose j * 2 ^ j else 0 := by
        rw [show (2 : ℕ[X]) ^ j * X ^ (n - j) * (n.choose j : ℕ[X]) =
          X ^ (n - j) * (↑(n.choose j * 2 ^ j : ℕ) : ℕ[X]) by
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            ac_rfl]
        simp only [← mul_assoc, coeff_mul_natCast, coeff_mul_X_pow', coeff_X_add_one_pow,
          Nat.cast_id]
        split_ifs <;> simp [mul_assoc]
      simp only [hcoeff]
      -- The shift must fit in degree b, and the remaining degree must be at most a.
      trans ∑ j ∈ Ico (n - b) (min (a + n + 1 - b) (n + 1)),
        if n - j ≤ b then a.choose (b - (n - j)) * n.choose j * 2 ^ j else 0
      · symm
        refine sum_subset ?_ fun j hj hmem ↦ ?_
        · intro j hj
          simp only [mem_Ico, mem_range] at hj ⊢
          omega
        · simp only [mem_range] at hj
          simp only [mem_Ico] at hmem
          by_cases h : n - j ≤ b
          · have hzero : a < b - (n - j) := by omega
            simp [h, Nat.choose_eq_zero_of_lt hzero]
          · simp [h]
      · refine sum_congr rfl fun j hj ↦ ?_
        simp only [mem_Ico] at hj
        rw [ite_eq_left (by omega)]

/-- **Unified power-of-two sums for generalized Delannoy numbers.** For natural numbers $k$, $m$,
$n$, write $D_k(m, n)$ and $D^k(m, n)$ for the lower and upper generalized Delannoy numbers. If
$m \ge k$ and $n \ge k$, then
$D_k(m, n) = \sum_{j=k}^{\min(m, n)} \binom{m-k}{j-k} \binom{n}{j} 2^j$; and, for all $k$, $m$, $n$,
$D^k(m, n) = \sum_{j=0}^{\min(m, n)} \binom{m+k}{j+k} \binom{n}{j} 2^j$.

With the convention $D_{-k} = D^k$, the second formula is the first with $k$ replaced by $-k$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 11
(`jis-2024-24.1.8-thm-11`). -/
public theorem genDelannoy_eq_sum_two_pow_unified (k m n : ℕ) :
    (k ≤ m → k ≤ n → genDelannoyLower k m n =
        ∑ j ∈ Ico k (min m n + 1), (m - k).choose (j - k) * n.choose j * 2 ^ j) ∧
      genDelannoyUpper k m n =
        ∑ j ∈ range (min m n + 1), (m + k).choose (j + k) * n.choose j * 2 ^ j := by
  constructor
  · intro hm hn
    rw [genDelannoyLower, show m + n - k = m - k + n by omega, sum_choose_eq_sum_two_pow,
      Nat.sub_sub_self hn, show m - k + n + 1 - (n - k) = m + 1 by omega, Nat.succ_min_succ]
    refine sum_congr rfl fun j hj ↦ ?_
    have hjn : j ≤ n := by rw [mem_Ico] at hj; omega
    rw [show n - k - (n - j) = j - k by omega]
  · rw [genDelannoyUpper, add_right_comm m n k, sum_choose_eq_sum_two_pow,
      show n - (n + k) = 0 by omega, show m + k + n + 1 - (n + k) = m + 1 by omega,
      Nat.succ_min_succ, Nat.Ico_zero_eq_range]
    refine sum_congr rfl fun j hj ↦ ?_
    have hjn : j ≤ n := by rw [mem_range] at hj; omega
    rw [show n + k - (n - j) = j + k by omega]

/-- **Lower generalized Delannoy numbers as a sum of powers of two.** For natural numbers $k$, $m$,
$n$ with $m \ge k$ and $n \ge k$, the lower generalized Delannoy number $D_k(m, n)$ satisfies
$D_k(m, n) = \sum_{j=0}^{\min(m-k, n-k)} \binom{m-k}{j} \binom{n}{j+k} 2^{j+k}$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 9
(`jis-2024-24.1.8-thm-9`). -/
public theorem genDelannoyLower_eq_sum_two_pow (k m n : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
    genDelannoyLower k m n =
      ∑ j ∈ range (min (m - k) (n - k) + 1), (m - k).choose j * n.choose (j + k) * 2 ^ (j + k) := by
  have htop : min m n + 1 - k = min (m - k) (n - k) + 1 := by omega
  rw [(genDelannoy_eq_sum_two_pow_unified k m n).1 hm hn, sum_Ico_eq_sum_range, htop]
  simp only [Nat.add_comm k, Nat.add_sub_cancel]

/-- **Powers-of-two formula for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$,
$$D^k(m, n) = \sum_{j=0}^{\min(m, n)} \binom{m + k}{j + k} \binom{n}{j} 2^j.$$

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 10
(`jis-2024-24.1.8-thm-10`). -/
public theorem genDelannoyUpper_eq_sum_two_pow (k m n : ℕ) :
    genDelannoyUpper k m n =
      ∑ j ∈ range (min m n + 1), (m + k).choose (j + k) * n.choose j * 2 ^ j :=
  (genDelannoy_eq_sum_two_pow_unified k m n).2

/-- **An upper generalized Delannoy number equal to $13$.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. Then $D^0(2, 2) = 13$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Table 1. -/
public theorem genDelannoyUpper_zero_two_two : genDelannoyUpper 0 2 2 = 13 := by decide

/-- **An upper generalized Delannoy number equal to $44$.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. Then $D^1(3, 2) = 44$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Table 1. -/
public theorem genDelannoyUpper_one_three_two : genDelannoyUpper 1 3 2 = 44 := by decide

/-- **A value of the lower generalized Delannoy number.** The lower generalized Delannoy number
$D_1(2, 2)$ equals $8$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1
(central theorem `D_k(m, n) = 2^k D^k(n - k, m - k)`). -/
public theorem genDelannoyLower_one_two_two : genDelannoyLower 1 2 2 = 8 := by decide

/-- **The lower and upper generalized Delannoy numbers agree at index zero.** For natural
numbers $k$, $m$ and $n$, let
$D_k(m, n) = \sum_{j=0}^{n} \binom{m + n - k - j}{n - k} \binom{n}{j}$ (with subtraction
truncated at $0$) and
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ be the lower
and upper generalized Delannoy numbers. Then $D_0(m, n) = D^0(m, n)$ for all natural numbers
$m$ and $n$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1. -/
public theorem genDelannoyLower_zero (m n : ℕ) :
    genDelannoyLower 0 m n = genDelannoyUpper 0 m n := by
  simp [genDelannoyLower, genDelannoyUpper]

/-- **Horizontal sum identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$,
$D^k(m, n) + D^k(m, n + 1) = 2 D^{k+1}(m, n)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 3
(`jis-2024-24.1.8-thm-3`). -/
public theorem genDelannoyUpper_add_succ_right (k m n : ℕ) :
    genDelannoyUpper k m n + genDelannoyUpper k m (n + 1) = 2 * genDelannoyUpper (k + 1) m n := by
  have hsplit : genDelannoyUpper k m (n + 1) = genDelannoyUpper (k + 1) m n +
      ∑ j ∈ range (n + 1), (m + n + k - j).choose (n + k + 1) * n.choose j := by
    simpa only [genDelannoyUpper, ← Nat.add_assoc, Nat.add_right_comm _ 1 k,
      Nat.add_sub_add_right, Nat.cast_id, Nat.mul_comm] using
      sum_choose_succ_mul (fun j _ ↦ (m + n + k + 1 - j).choose (n + k + 1)) n
  rw [hsplit, add_left_comm, two_mul]
  congr 1
  unfold genDelannoyUpper
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [← Nat.add_mul, ← Nat.choose_succ_succ']
  have hj' := mem_range.mp hj
  congr 2
  omega

/-- **Vertical sum identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$ with $k \ge 1$,
$D^k(m, n) + D^k(m + 1, n) = D^{k-1}(m + 1, n + 1)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 4
(`jis-2024-24.1.8-thm-4`). -/
public theorem genDelannoyUpper_add_succ_left (k m n : ℕ) (hk : 1 ≤ k) :
    genDelannoyUpper k m n + genDelannoyUpper k (m + 1) n =
      genDelannoyUpper (k - 1) (m + 1) (n + 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [add_comm (genDelannoyUpper (s + 1) m n)]
  simp only [Nat.add_sub_cancel]
  have hsplit := sum_choose_succ_mul
    (fun j _ ↦ (m + n + (s + 1) + 1 - j).choose (n + (s + 1))) n
  have htop : m + 1 + n + (s + 1) = m + n + (s + 1) + 1 := by omega
  have htop' : m + 1 + (n + 1) + s = m + n + (s + 1) + 1 := by omega
  have hbot : n + 1 + s = n + (s + 1) := by omega
  simpa only [genDelannoyUpper, htop, htop', hbot, Nat.add_sub_add_right, Nat.cast_id,
    Nat.mul_comm] using hsplit.symm

/-- **Vertical difference identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$ with $k \ge 1$,
$D^k(m + 1, n) - D^k(m, n) = D^{k-1}(m + 1, n)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Corollary 6
(`jis-2024-24.1.8-cor-6`). -/
public theorem genDelannoyUpper_succ_left_sub (k m n : ℕ) (hk : 1 ≤ k) :
    (genDelannoyUpper k (m + 1) n : ℤ) - genDelannoyUpper k m n =
      genDelannoyUpper (k - 1) (m + 1) n := by
  have hv := genDelannoyUpper_add_succ_left k m n hk
  have hh := genDelannoyUpper_add_succ_right (k - 1) (m + 1) n
  rw [Nat.sub_add_cancel hk] at hh
  omega

/-- **Horizontal difference identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$ with $m \ge 1$,
$D^k(m, n + 1) - D^k(m, n) = 2 D^{k+1}(m - 1, n)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Corollary 5
(`jis-2024-24.1.8-cor-5`). -/
public theorem genDelannoyUpper_succ_right_sub (k m n : ℕ) (hm : 1 ≤ m) :
    (genDelannoyUpper k m (n + 1) : ℤ) - genDelannoyUpper k m n =
      2 * genDelannoyUpper (k + 1) (m - 1) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hpascal : genDelannoyUpper (k + 1) (m + 1) n =
      genDelannoyUpper k (m + 1) n + genDelannoyUpper (k + 1) m n := by
    unfold genDelannoyUpper
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    have htop : m + n + (k + 1) - j = m + 1 + n + k - j := by omega
    have hsucc : m + 1 + n + (k + 1) - j = m + 1 + n + k - j + 1 := by omega
    rw [hsucc, htop, ← Nat.add_assoc n k 1, ← Nat.add_mul, Nat.choose_succ_succ']
  have hsum := genDelannoyUpper_add_succ_right k (m + 1) n
  simp only [Nat.add_sub_cancel]
  omega

/-- **Parity of a sum of adjacent binomial coefficients.** For all natural numbers $n$ and $k$
with $k \ge 1$, $\binom{n}{k} + \binom{n+1}{k} \equiv \binom{n}{k-1} \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Lemma 15
(`jis-2024-24.1.8-lem-15`). -/
public theorem choose_add_choose_succ_modEq_two (n k : ℕ) (hk : 1 ≤ k) :
    n.choose k + (n + 1).choose k ≡ n.choose (k - 1) [MOD 2] := by
  rw [Nat.choose_succ_left n k hk, ← add_assoc, add_right_comm, ← Nat.two_mul]
  exact Nat.ModEq.modulus_mul_add

private def horizontalSum (S : ℕ → ℕ → ℤ) (m n : ℕ) : ℤ :=
  S m n + S m (n + 1)

-- Adjacent rows of a horizontal sum differ by twice the lower entry before summing.
private theorem iterate_horizontalSum_succ_row (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n)
    (i m n : ℕ) :
    horizontalSum^[i + 1] R (m + 1) n =
      horizontalSum^[i + 1] R m n + 2 * horizontalSum^[i] R (m + 1) n := by
  induction i generalizing n with
  | zero =>
    change R (m + 1) n + R (m + 1) (n + 1) = R m n + R m (n + 1) + 2 * R (m + 1) n
    rw [hR]
    omega
  | succ i ih =>
    have hn := ih n
    have hn' := ih (n + 1)
    simp only [Function.iterate_succ_apply', horizontalSum] at hn hn' ⊢
    omega

/-- **Rows of iterated horizontal sums of a Delannoy array agree mod 2.** Let $R(m, n)$, for
$m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all
$m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for the
$i$-fold horizontal sum. Then for every $i \ge 1$ and all $m, m', n \in \mathbb{N}$,
$R^i(m, n) \equiv R^i(m', n) \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Corollary 14
(`jis-2024-24.1.8-cor-14`). -/
public theorem delannoyArray_horizontalSum_rows_modEq (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (i : ℕ) (hi : 1 ≤ i)
    (m m' n : ℕ) :
    (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[i] R m n ≡
      (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[i] R m' n [ZMOD 2] := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
  have row_zero (a : ℕ) : horizontalSum^[j + 1] R a n ≡ horizontalSum^[j + 1] R 0 n [ZMOD 2] := by
    induction a with
    | zero => rfl
    | succ a ih => rwa [iterate_horizontalSum_succ_row R hR j a n, Int.add_modulus_mul_modEq_iff]
  exact (row_zero m).trans (row_zero m').symm

private theorem iterate_horizontalSum_seed (R : ℕ → ℕ → ℤ) (k : ℕ)
    (hseed : ∀ n, R 0 n = (k + n).choose k) (j : ℕ) (hj : j ≤ k) (n : ℕ) :
    horizontalSum^[j] R 0 n ≡ ((k + n).choose (k - j) : ℤ) [ZMOD 2] := by
  induction j generalizing n with
  | zero => simp [hseed]
  | succ j ih =>
    have h := ih (by omega) n
    have h' := ih (by omega) (n + 1)
    rw [Function.iterate_succ_apply']
    apply (h.add h').trans
    have hchoose := choose_add_choose_succ_modEq_two (k + n) (k - j) (by omega)
    simpa [Nat.add_assoc, Nat.sub_sub] using Int.natCast_modEq_iff.mpr hchoose

/-- **Parity of iterated horizontal sums of a Delannoy array with binomial seeds.** Let $R(m, n)$,
for $m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for
all $m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for
the $i$-fold horizontal sum, so $R^0 = R$. Let $k \in \mathbb{N}$ and suppose
$R(0, n) = \binom{k+n}{k}$ for all $n$; the values $R(m, 0)$ for $m \ge 1$ are arbitrary. Then
every entry of $R^{k+1}$ is even, and for every $j \le k$ some entry of $R^j$ is odd.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Lemma 16
(`jis-2024-24.1.8-lem-16`). -/
public theorem delannoyArray_binomial_seeds_parity (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (k : ℕ)
    (hseed : ∀ n, R 0 n = (k + n).choose k) :
    (∀ m n, (2 : ℤ) ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[k + 1] R m n) ∧
      ∀ j ≤ k, ∃ m n,
        ¬ (2 : ℤ) ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[j] R m n := by
  have hlast (n : ℕ) : horizontalSum^[k] R 0 n ≡ 1 [ZMOD 2] := by
    simpa using iterate_horizontalSum_seed R k hseed k le_rfl n
  constructor
  · intro m n
    change 2 ∣ horizontalSum^[k + 1] R m n
    induction m with
    | zero =>
      rw [Function.iterate_succ_apply']
      have h := (hlast n).add (hlast (n + 1))
      exact h.dvd_iff.mpr (by decide)
    | succ m ih =>
      rw [iterate_horizontalSum_succ_row R hR k m n]
      exact Int.dvd_add ih (dvd_mul_right ..)
  · intro j hj
    change ∃ m n, ¬ (2 : ℤ) ∣ horizontalSum^[j] R m n
    induction hj using Nat.decreasingInduction with
    | self =>
      refine ⟨0, 0, ?_⟩
      rw [(hlast 0).dvd_iff]
      decide
    | of_succ j _ ih =>
      obtain ⟨m, n, hn⟩ := ih
      rw [Function.iterate_succ_apply'] at hn
      by_cases h : (2 : ℤ) ∣ horizontalSum^[j] R m n
      · exact ⟨m, n + 1, fun h' => hn (Int.dvd_add h h')⟩
      · exact ⟨m, n, h⟩

/-- **First horizontal sums of a Delannoy array with binomial seeds.** Let $R(m, n)$, for
$m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all
$m, n$. Let $k \ge 1$ and suppose $R(0, n) = \binom{k+n}{k}$ for all $n$. Then for all $m$ and
$n$, $R(m, n) + R(m, n+1) \equiv \binom{k+n}{k-1} \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 17
(`jis-2024-24.1.8-thm-17`). -/
public theorem delannoyArray_binomial_seeds_horizontalSum_modEq (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (k : ℕ) (hk : 1 ≤ k)
    (hseed : ∀ n, R 0 n = (k + n).choose k) (m n : ℕ) :
    R m n + R m (n + 1) ≡ (k + n).choose (k - 1) [ZMOD 2] := by
  exact (delannoyArray_horizontalSum_rows_modEq R hR 1 le_rfl m 0 n).trans
    (iterate_horizontalSum_seed R k hseed 1 hk n)

private theorem iterate_horizontalSum_zero_congr (R S : ℕ → ℕ → ℤ)
    (h : ∀ n, R 0 n = S 0 n) (p n : ℕ) :
    horizontalSum^[p] R 0 n = horizontalSum^[p] S 0 n := by
  induction p generalizing n with
  | zero => exact h n
  | succ p ih => simp only [Function.iterate_succ_apply', horizontalSum, ih]

private theorem iterate_horizontalSum_one (p n : ℕ) :
    horizontalSum^[p] (fun _ _ => (1 : ℤ)) 0 n = 2 ^ p := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply', horizontalSum, ih, ih, pow_succ', two_mul]

private theorem two_pow_dvd_iterate_horizontalSum_choose (k p d n : ℕ) :
    (2 : ℤ) ^ (p - d) ∣ horizontalSum^[p] (fun _ b => ((k + b).choose d : ℤ)) 0 n := by
  -- Pascal's identity gives twice the same binomial row plus the row of one lower degree.
  have hpascal (p d n : ℕ) :
      horizontalSum^[p + 1] (fun _ b => ((k + b).choose (d + 1) : ℤ)) 0 n =
        2 * horizontalSum^[p] (fun _ b => ((k + b).choose (d + 1) : ℤ)) 0 n +
          horizontalSum^[p] (fun _ b => ((k + b).choose d : ℤ)) 0 n := by
    induction p generalizing n with
    | zero =>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, horizontalSum,
        ← Nat.add_assoc, Nat.choose_succ_succ', Nat.cast_add, two_mul]
      omega
    | succ p ih =>
      have hn := ih n
      have hn' := ih (n + 1)
      simp only [Function.iterate_succ_apply', horizontalSum] at hn hn' ⊢
      omega
  induction p generalizing d with
  | zero => simp
  | succ p ih =>
    by_cases h : p + 1 ≤ d
    · simp [Nat.sub_eq_zero_of_le h]
    cases d with
    | zero => simp [iterate_horizontalSum_one]
    | succ d =>
      rw [hpascal, Nat.add_sub_add_right]
      refine Int.dvd_add ?_ (ih d)
      rw [show p - d = p - (d + 1) + 1 by omega, pow_succ']
      exact mul_dvd_mul_left _ (ih (d + 1))

/-- **Powers of two dividing iterated horizontal sums of a Delannoy array.** Let $R(m, n)$, for
$m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all
$m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for the
$i$-fold horizontal sum. Let $k, i \in \mathbb{N}$ with $i \ge 1$, and suppose
$R(0, n) = \binom{k+n}{k}$ for all $n$. Then every entry of $R^{k+i}$ is divisible by $2^i$, and
some entry of $R^{k+i}$ is not divisible by $2^{i+1}$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 18
(`jis-2024-24.1.8-thm-18`). -/
public theorem delannoyArray_binomial_seeds_two_pow_dvd (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (k i : ℕ) (hi : 1 ≤ i)
    (hseed : ∀ n, R 0 n = (k + n).choose k) :
    (∀ m n, (2 : ℤ) ^ i ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[k + i] R m n) ∧
      ∃ m n, ¬ (2 : ℤ) ^ (i + 1) ∣
        (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[k + i] R m n := by
  change (∀ m n, (2 : ℤ) ^ i ∣ horizontalSum^[k + i] R m n) ∧
    ∃ m n, ¬ (2 : ℤ) ^ (i + 1) ∣ horizontalSum^[k + i] R m n
  constructor
  · intro m n
    induction i, hi using Nat.le_induction generalizing m with
    | base =>
      rw [pow_one]
      exact (delannoyArray_binomial_seeds_parity R hR k hseed).1 m n
    | succ i _ ih =>
      induction m with
      | zero =>
        rw [iterate_horizontalSum_zero_congr R (fun _ b => ((k + b).choose k : ℤ)) hseed]
        simpa only [Nat.add_sub_cancel_left] using
          two_pow_dvd_iterate_horizontalSum_choose k (k + (i + 1)) k n
      | succ m hm =>
        rw [← Nat.add_assoc, iterate_horizontalSum_succ_row R hR (k + i) m n]
        exact Int.dvd_add hm (by rw [pow_succ']; exact mul_dvd_mul_left _ (ih (m + 1)))
  · by_cases hk : k = 0
    · subst k
      have hone (n : ℕ) : R 0 n = 1 := by simp [hseed]
      refine ⟨0, 0, ?_⟩
      rw [Nat.zero_add, iterate_horizontalSum_zero_congr R (fun _ _ => 1) hone,
        iterate_horizontalSum_one]
      have htwo : (2 : ℤ) ≠ 0 := by decide
      have h := mul_dvd_mul_iff_left (pow_ne_zero i htwo) (b := (2 : ℤ)) (c := 1)
      rw [← pow_succ, mul_one] at h
      exact fun hd => (by decide : ¬ (2 : ℤ) ∣ 1) (h.mp hd)
    -- A tail of divisible entries in column zero would give such a tail one level lower.
    have sharp (j b : ℕ) : ∃ m ≥ b, ¬ (2 : ℤ) ^ (j + 1) ∣ horizontalSum^[k + j] R m 0 := by
      induction j generalizing b with
      | zero =>
        refine ⟨b, le_rfl, ?_⟩
        have h : horizontalSum^[k] R 0 0 ≡ 1 [ZMOD 2] := by
          simpa using iterate_horizontalSum_seed R k hseed k le_rfl 0
        have hb : horizontalSum^[k] R b 0 ≡ horizontalSum^[k] R 0 0 [ZMOD 2] :=
          delannoyArray_horizontalSum_rows_modEq R hR k (Nat.pos_of_ne_zero hk) b 0 0
        change ¬ (2 : ℤ) ∣ horizontalSum^[k] R b 0
        rw [(hb.trans h).dvd_iff]
        decide
      | succ j ih =>
        by_contra! hall
        obtain ⟨m, hm, hn⟩ := ih (b + 1)
        cases m with
        | zero => omega
        | succ m =>
          have hupper := hall (m + 1) (by omega)
          have hlower := hall m (by omega)
          rw [← Nat.add_assoc k j 1] at hupper hlower
          rw [iterate_horizontalSum_succ_row R hR (k + j) m 0] at hupper
          have hd := (Int.dvd_add_right hlower).mp hupper
          rw [pow_succ'] at hd
          exact hn ((mul_dvd_mul_iff_left (by decide : (2 : ℤ) ≠ 0)).mp hd)
    obtain ⟨m, _, hm⟩ := sharp i 0
    exact ⟨m, 0, hm⟩

end MetaMathlibExt.DelannoyConstructions

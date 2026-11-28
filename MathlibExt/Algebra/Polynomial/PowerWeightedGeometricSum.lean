/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Order.Interval.Finset.Nat
import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSum

/-!
# Rational form of the power-weighted geometric sum

For positive integers `t` and `k`, multiplication by `(1 - X) ^ (t + 1)` expresses
`∑ n ∈ Finset.Icc 1 k, C ((n : ℤ) ^ t) * X ^ n` as the sum of two polynomials supported in
degrees `1` through `t` and `k + 1` through `k + t + 1`, respectively. The two contributions
are added even in degrees where the ranges overlap.

## References

* Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered Partitions
  Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, pp. 1–11, Lemma 4.
  <https://math.colgate.edu/~integers/y12/y12.pdf>
* Hidefumi Katsuura, *Summations Involving Binomial Coefficients*, The College Mathematics
  Journal 40(4) (2009), pp. 275–278. The alternating-sum vanishing used in Lemma 4 is quoted as
  Theorem 3 by Vishwakarma and Singh and is available as `sum_neg_one_pow_choose_mul_pow`
  in `MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSum`.
-/

namespace MetaMathlibExt

open Finset Polynomial

-- The proof also works for k = 0; keep the positivity hypothesis of Lemma 4.
set_option linter.unusedVariables false in
/-- **Rational form of the power-weighted geometric sum.** For positive integers $t$ and $k$,
the following identity holds in $\mathbb{Z}[X]$:

$$(1 - X)^{t+1} \sum_{n=1}^{k} n^t X^n =
\sum_{n=1}^{t} \Bigl(\sum_{i=0}^{n-1} (-1)^i \binom{t+1}{i} (n - i)^t\Bigr) X^n +
\sum_{m=1}^{t+1} \Bigl(\sum_{i=m}^{t+1} (-1)^i \binom{t+1}{i} (k + m - i)^t\Bigr) X^{k+m}.$$

Reducing the coefficients modulo a prime $p$ and evaluating at $x \in \mathbb{F}_p$ with $x \ne 1$
gives the formula in the source: $h_t^k(x) = \sum_{n=1}^{k} n^t x^n$ is the right-hand side
evaluated at $x$ divided by $(1 - x)^{t+1}$. Pointwise equality at a fixed prime does not recover
the polynomial identity: even over $\mathbb{F}_p$, $X^p - X$ is nonzero as a polynomial but
vanishes at every field element.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 4
(`integers-2024-A12-lem-4`). -/
public theorem one_sub_X_pow_mul_sum_pow_mul_X_pow (t k : ℕ) (ht : 0 < t) (hk : 0 < k) :
    (1 - X : ℤ[X]) ^ (t + 1) * ∑ n ∈ Finset.Icc 1 k, C ((n : ℤ) ^ t) * X ^ n =
      ∑ n ∈ Finset.Icc 1 t, C (∑ i ∈ Finset.range n,
          (-1) ^ i * ((t + 1).choose i : ℤ) * ((n : ℤ) - i) ^ t) * X ^ n +
        ∑ m ∈ Finset.Icc 1 (t + 1), C (∑ i ∈ Finset.Icc m (t + 1),
          (-1) ^ i * ((t + 1).choose i : ℤ) * ((k : ℤ) + m - i) ^ t) * X ^ (k + m) := by
  let a (i : ℕ) : ℤ := (-1) ^ i * ((t + 1).choose i : ℤ)
  let w (q i : ℕ) : ℤ := a i * ((q : ℤ) - i) ^ t
  have hbinomial : (1 - X : ℤ[X]) ^ (t + 1) =
      ∑ i ∈ range (t + 2), C (a i) * X ^ i := by
    rw [sub_eq_add_neg, add_comm (1 : ℤ[X]) (-X), add_pow]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [a, map_mul, map_pow, map_neg, map_one, map_natCast,
      one_pow, mul_one, ← neg_one_mul (X : ℤ[X]), mul_pow, mul_right_comm]
  have hcoeff (s : Finset ℕ) (f : ℕ → ℤ) (d : ℕ) :
      (∑ n ∈ s, C (f n) * X ^ n).coeff d = if d ∈ s then f d else 0 := by
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, sum_ite_eq]
  ext q
  have hzero : ∑ i ∈ range (t + 2), w q i = 0 := by
    apply Int.cast_injective (α := ℂ)
    simp only [w, a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_sub, Int.cast_natCast, Int.cast_zero]
    simpa only [one_mul, mul_neg, mul_one, sub_eq_add_neg] using
      (sum_neg_one_pow_choose_mul_pow (q : ℂ) (-1) 1 (n := t + 1) (m := t)
        (Nat.succ_pos t) ht).2 (Nat.lt_succ_self t)
  -- The window 1 ≤ q - i ≤ k is the difference of two strict cutoffs on i.
  have hwindow : (∑ i ∈ range (t + 2), (C (a i) * X ^ i *
      ∑ n ∈ Icc 1 k, C ((n : ℤ) ^ t) * X ^ n).coeff q) =
      (∑ i ∈ range (t + 2), if i < q then w q i else 0) -
        ∑ i ∈ range (t + 2), if i < q - k then w q i else 0 := by
    simp_rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', hcoeff]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    by_cases hi : i < q
    · have hmem : q - i ∈ Icc 1 k ↔ ¬i < q - k := by
        simp only [mem_Icc]
        omega
      by_cases hik : i < q - k <;> simp [hi, hi.le, hmem, hik, Int.natCast_sub hi.le, w]
    · have hmem : q - i ∉ Icc 1 k := by
        simp only [mem_Icc]
        omega
      have hik : ¬i < q - k := fun h ↦ hi (h.trans_le (Nat.sub_le q k))
      simp [hmem, hi, hik]
  rw [hbinomial, sum_mul, finsetSum_coeff, hwindow, coeff_add, hcoeff]
  have hlow : (∑ i ∈ range (t + 2), if i < q then w q i else 0) =
      if q ∈ Icc 1 t then ∑ i ∈ range q, w q i else 0 := by
    by_cases hq : q ∈ Icc 1 t
    · rw [ite_eq_left hq, ← sum_filter]
      congr 1
      ext i
      simp only [mem_filter, mem_range]
      have hqt := (mem_Icc.mp hq).2
      omega
    · rw [ite_eq_right hq]
      by_cases hq0 : q = 0
      · simp [hq0]
      · refine Eq.trans (sum_congr rfl fun i hi ↦ ?_) hzero
        by_cases hiq : i < q
        · rw [ite_eq_left hiq]
        · have heq : i = q := by
            simp only [mem_Icc] at hq
            simp only [mem_range] at hi
            omega
          simp [heq, w, zero_pow ht.ne']
  have hhigh : -(∑ i ∈ range (t + 2), if i < q - k then w q i else 0) =
      ∑ i ∈ Icc (q - k) (t + 1), w q i := by
    have hrange : (range (t + 2)).filter (fun i ↦ q - k ≤ i) = Icc (q - k) (t + 1) := by
      ext i
      simp only [mem_filter, mem_range, mem_Icc]
      omega
    rw [← hrange, sum_filter]
    calc
      _ = (∑ i ∈ range (t + 2), w q i) - ∑ i ∈ range (t + 2), if i < q - k then w q i else 0 := by
        rw [hzero, zero_sub]
      _ = _ := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun i _ ↦ ?_
        by_cases hi : i < q - k <;> simp [hi, not_le.mpr, le_of_not_gt]
  -- Convert the complementary cutoff into the coefficient of the shifted sum.
  have htail : (∑ m ∈ Icc 1 (t + 1), C (∑ i ∈ Icc m (t + 1), w (k + m) i) *
      X ^ (k + m)).coeff q = ∑ i ∈ Icc (q - k) (t + 1), w q i := by
    simp_rw [add_comm k, pow_add, ← mul_assoc]
    rw [← sum_mul, coeff_mul_X_pow', hcoeff]
    by_cases hqk : k < q
    · rw [ite_eq_left hqk.le]
      by_cases hm : q - k ∈ Icc 1 (t + 1)
      · simp only [ite_eq_left hm, Nat.sub_add_cancel hqk.le]
      · have hempty : Icc (q - k) (t + 1) = ∅ := by
          apply Icc_eq_empty
          simp only [mem_Icc] at hm
          omega
        simp [hm, hempty]
    · have hqk' : q ≤ k := le_of_not_gt hqk
      have heq : Icc 0 (t + 1) = range (t + 2) := by
        ext i
        simp only [mem_Icc, zero_le, true_and, mem_range]
        omega
      rw [Nat.sub_eq_zero_of_le hqk', heq, hzero]
      simp
  rw [hlow, sub_eq_add_neg, hhigh, ← htail]
  simp only [w, a, Nat.cast_add]

end MetaMathlibExt

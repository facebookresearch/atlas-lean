/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Coeff
import MathlibExt.NumberTheory.Recurrences.GFPFibSumChoose
import MathlibExt.NumberTheory.Recurrences.GFPLucasCatalan
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Even binomial coefficients as alternating sums

The specialization `d = 2`, `g = X - 1` gives `4 * g + d ^ 2 = 4 * X`. We expand
the same Lucas-type polynomial in powers of `X` and of `X - 1`, and compare coefficients
before any evaluation of `X`.
-/

namespace MetaMathlibExt

open Finset Polynomial

private theorem lucas_succ_eq (g : ℤ[X]) (m : ℕ) :
    generalizedFibonacciPolynomial 2 2 2 g (m + 1) =
      generalizedFibonacciPolynomial 0 1 2 g (m + 2) +
        g * generalizedFibonacciPolynomial 0 1 2 g m := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp; ring
  | more m ih₀ ih₁ =>
    rw [show m + 2 + 1 = m + 1 + 2 by omega, generalizedFibonacciPolynomial_add_two,
      ih₁, ih₀, generalizedFibonacciPolynomial_add_two 0 1 2 g (m + 2),
      generalizedFibonacciPolynomial_add_two 0 1 2 g m]
    ring

private def lucasChoose (n i : ℕ) : ℕ :=
  (n - i).choose i + if i = 0 then 0 else (n - i - 1).choose (i - 1)

private theorem lucasChoose_cast {n i : ℕ} (hn : 0 < n) (hi : i ≤ n / 2) :
    (lucasChoose n i : ℚ) = n / ((n : ℚ) - i) * ((n - i).choose i : ℚ) := by
  have hpos : 0 < (n : ℚ) - i := sub_pos.mpr (by exact_mod_cast (show i < n by omega))
  cases i with
  | zero => simp [lucasChoose, ne_of_gt hn]
  | succ j =>
    have h := congrArg (fun a : ℕ ↦ (a : ℚ)) (Nat.add_one_mul_choose_eq (n - (j + 1) - 1) j)
    rw [show n - (j + 1) - 1 + 1 = n - (j + 1) by omega] at h
    push_cast [Nat.cast_sub (show j + 1 ≤ n by omega)] at h
    push_cast at hpos
    simp only [lucasChoose, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, Nat.cast_add,
      Nat.cast_one]
    rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
    linear_combination h

private theorem lucas_eq_shifted_sum (g : ℤ[X]) {n : ℕ} (hn : 2 ≤ n) :
    generalizedFibonacciPolynomial 2 2 2 g n =
      ∑ i ∈ range (n / 2 + 1), C ((lucasChoose n i : ℤ) * 2 ^ (n - 2 * i)) * g ^ i := by
  have h := lucas_succ_eq g (n - 1)
  rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega,
    gfp_fib_eq_sum_choose 2 g (show 1 ≤ n + 1 by omega),
    gfp_fib_eq_sum_choose 2 g (show 1 ≤ n - 1 by omega),
    Nat.add_sub_cancel, show (n - 1 - 1) / 2 + 1 = n / 2 by omega] at h
  rw [h, sum_range_succ', sum_range_succ' (fun i ↦ C _ * g ^ i), mul_sum, add_right_comm,
    ← sum_add_distrib]
  congr 1
  · apply sum_congr rfl
    intro i _
    simp only [lucasChoose, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, map_mul, map_pow,
      map_ofNat, Nat.cast_add, map_add, C_eq_natCast,
      show n + 1 - (i + 1) - 1 = n - (i + 1) by omega,
      show n + 1 - 2 * (i + 1) - 1 = n - 2 * (i + 1) by omega,
      show n - 1 - i - 1 = n - (i + 1) - 1 by omega,
      show n - 1 - 2 * i - 1 = n - 2 * (i + 1) by omega, pow_succ g]
    ring
  · simp [lucasChoose]

private theorem lucas_eq_even_sum (n : ℕ) :
    generalizedFibonacciPolynomial 2 2 2 (X - 1) n =
      2 * ∑ i ∈ range (n / 2 + 1), C (n.choose (2 * i) : ℤ) * X ^ i := by
  have h := gfp_lucas_catalan (α := 1) (p₀ := 2) (p₁ := 2) (d := 2) (by norm_num)
    (by simp) (X - 1) n
  simp only [map_one, mul_one, map_ofNat,
    show (4 : ℤ[X]) * (X - 1) + 2 ^ 2 = 2 ^ 2 * X by ring] at h
  have h2 : (2 : ℤ[X]) ≠ 0 := by
    rw [show (2 : ℤ[X]) = C (2 : ℤ) by simp, ne_eq, C_eq_zero]
    decide
  apply mul_left_cancel₀ (pow_ne_zero n h2)
  rw [h, mul_left_comm (2 ^ n) 2]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have : 2 * i ≤ n := by have := mem_range.mp hi; omega
  rw [mul_pow, ← pow_mul, C_eq_natCast]
  calc
    _ = (n.choose (2 * i) : ℤ[X]) * (2 ^ (n - 2 * i) * 2 ^ (2 * i)) * X ^ i := by ring
    _ = _ := by rw [← pow_add, show n - 2 * i + 2 * i = n by omega]; ring

private theorem coeff_shifted_sum (n k : ℕ) :
    (∑ i ∈ range (n / 2 + 1), C ((lucasChoose n i : ℤ) * 2 ^ (n - 2 * i)) *
      (X - 1) ^ i).coeff k =
      ∑ i ∈ Icc k (n / 2), (lucasChoose n i : ℤ) * 2 ^ (n - 2 * i) *
        ((-1) ^ (i - k) * (i.choose k : ℤ)) := by
  rw [show (X - 1 : ℤ[X]) = X + C (-1) by simp [sub_eq_add_neg], finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_add_C_pow]
  symm
  refine sum_subset (fun i hi ↦ mem_range.mpr (by have := (mem_Icc.mp hi).2; omega)) ?_
  intro i hi hik
  have : i < k := by
    have := mem_range.mp hi
    simp only [mem_Icc, not_and_or, not_le] at hik
    omega
  simp [Nat.choose_eq_zero_of_lt this]

/-- **Binomial coefficients of even lower index as an alternating sum.** For natural numbers $n$
and $k$ with $k < \lfloor n/2 \rfloor$,
$$\binom{n}{2k} = n \sum_{i=k}^{\lfloor n/2 \rfloor} \frac{(-1)^{i-k}}{n-i} \, 2^{n-2i-1}
  \binom{n-i}{i} \binom{i}{k},$$
an identity of rational numbers in which the exponent $n-2i-1$ may be $-1$.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (3) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem choose_two_mul_eq_alternating_sum {n k : ℕ} (hk : k < n / 2) :
    (n.choose (2 * k) : ℚ) =
      n * ∑ i ∈ Icc k (n / 2),
        (-1) ^ (i - k) / ((n : ℚ) - i) * (2 : ℚ) ^ ((n : ℤ) - 2 * i - 1) *
          ((n - i).choose i : ℚ) * (i.choose k : ℚ) := by
  have hz := congrArg (fun p : ℤ[X] ↦ p.coeff k) <|
    (lucas_eq_even_sum n).symm.trans (lucas_eq_shifted_sum (X - 1) (n := n) (by omega))
  rw [coeff_shifted_sum, show (2 : ℤ[X]) = C (2 : ℤ) by simp, coeff_C_mul, finsetSum_coeff] at hz
  simp only [coeff_C_mul_X_pow, sum_ite_eq, mem_range.mpr (by omega : k < n / 2 + 1),
    ite_true] at hz
  have hq := congrArg (Int.castRingHom ℚ) hz
  simp only [map_mul, map_sum, map_pow, map_ofNat, map_neg, map_one] at hq
  simp only [Int.coe_castRingHom, Int.cast_natCast] at hq
  calc
    _ = (∑ i ∈ Icc k (n / 2), (lucasChoose n i : ℚ) * 2 ^ (n - 2 * i) *
          ((-1) ^ (i - k) * (i.choose k : ℚ))) / 2 := by
      rw [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0), mul_comm]
      exact hq
    _ = _ := by
      rw [div_eq_mul_inv, sum_mul, mul_sum]
      apply sum_congr rfl
      intro i hi
      have hi' := (mem_Icc.mp hi).2
      have he : ((n - 2 * i : ℕ) : ℤ) = (n : ℤ) - 2 * i := by omega
      rw [lucasChoose_cast (by omega) hi', zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
        ← he, zpow_natCast, zpow_one, div_eq_mul_inv, div_eq_mul_inv]
      ring

end MetaMathlibExt

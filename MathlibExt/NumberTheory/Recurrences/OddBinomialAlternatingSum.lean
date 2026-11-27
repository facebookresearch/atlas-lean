/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.Ring

/-! # Odd binomial coefficients as alternating sums

The difference of the powers of `1 + X` and `1 - X` satisfies a second-order recurrence.
We solve it by Pascal's rule and take the coefficient of `X ^ (2 * k + 1)`.
-/

namespace MetaMathlibExt

open Finset Polynomial

private def weightedChoose (m i : ℕ) : ℤ :=
  2 ^ (m - 2 * i) * ((m - i).choose i : ℤ)

private theorem weightedChoose_zero (m : ℕ) : weightedChoose m 0 = 2 ^ m := by
  simp [weightedChoose]

private theorem weightedChoose_eq_zero {m i : ℕ} (h : m < 2 * i) : weightedChoose m i = 0 := by
  simp [weightedChoose, Nat.choose_eq_zero_of_lt (show m - i < i by omega)]

private theorem weightedChoose_step (m i : ℕ) :
    weightedChoose (m + 2) (i + 1) =
      2 * weightedChoose (m + 1) (i + 1) + weightedChoose m i := by
  by_cases h : m < 2 * i
  · rw [weightedChoose_eq_zero (by omega : m + 2 < 2 * (i + 1)),
      weightedChoose_eq_zero (by omega : m + 1 < 2 * (i + 1)), weightedChoose_eq_zero h]
    simp
  have hPascal : (m + 2 - (i + 1)).choose (i + 1) =
      (m - i).choose i + (m + 1 - (i + 1)).choose (i + 1) := by
    rw [show m + 2 - (i + 1) = (m - i) + 1 by omega, Nat.choose_succ_succ',
      show m + 1 - (i + 1) = m - i by omega]
  by_cases h' : m = 2 * i
  · rw [weightedChoose_eq_zero (by omega : m + 1 < 2 * (i + 1))]
    have hz : (m + 1 - (i + 1)).choose (i + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [weightedChoose, hPascal, hz, add_zero, mul_zero, zero_add, weightedChoose,
      show m + 2 - 2 * (i + 1) = m - 2 * i by omega]
  · simp only [weightedChoose, hPascal, Nat.cast_add,
      show m + 2 - 2 * (i + 1) = m - 2 * i by omega,
      show m - 2 * i = (m + 1 - 2 * (i + 1)) + 1 by omega, pow_succ]
    ring

-- The terms beyond `m / 2` vanish. Padding to `m` lets the recurrence use a fixed index shift.
private noncomputable def binomialPolynomial (g : ℤ[X]) (m : ℕ) : ℤ[X] :=
  ∑ i ∈ range (m + 1), C (weightedChoose m i) * g ^ i

private theorem binomialPolynomial_step (g : ℤ[X]) (m : ℕ) :
    binomialPolynomial g (m + 2) =
      2 * binomialPolynomial g (m + 1) + g * binomialPolynomial g m := by
  unfold binomialPolynomial
  rw [sum_range_succ (n := m + 2)]
  simp only [weightedChoose_eq_zero (by omega : m + 2 < 2 * (m + 2)), map_zero, zero_mul, add_zero]
  rw [sum_range_succ', sum_range_succ' (n := m + 1)]
  have hsum : (∑ i ∈ range (m + 1), C (weightedChoose (m + 2) (i + 1)) * g ^ (i + 1)) =
      2 * (∑ i ∈ range (m + 1), C (weightedChoose (m + 1) (i + 1)) * g ^ (i + 1)) +
      g * ∑ i ∈ range (m + 1), C (weightedChoose m i) * g ^ i := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    simp only [weightedChoose_step, map_add, map_mul, map_ofNat, pow_succ]
    ring
  rw [hsum]
  simp only [weightedChoose_zero, map_pow, map_ofNat, pow_zero, mul_one]
  rw [pow_succ (2 : ℤ[X]) (m + 1)]
  ring

private theorem pow_sub_eq (m : ℕ) :
    (1 + X : ℤ[X]) ^ (m + 1) - (1 - X) ^ (m + 1) =
      2 * X * binomialPolynomial (X ^ 2 - 1) m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [binomialPolynomial, weightedChoose]; ring
  | one =>
    rw [binomialPolynomial, sum_range_succ, sum_range_one,
      weightedChoose_eq_zero (by decide : 1 < 2 * 1)]
    simp [weightedChoose]
    ring
  | more m ih₀ ih₁ =>
    calc
      _ = 2 * ((1 + X : ℤ[X]) ^ (m + 1 + 1) - (1 - X) ^ (m + 1 + 1)) +
          (X ^ 2 - 1) * ((1 + X) ^ (m + 1) - (1 - X) ^ (m + 1)) := by
        simp only [pow_succ]
        ring
      _ = _ := by rw [ih₁, ih₀, binomialPolynomial_step]; ring

private theorem coeff_one_sub_X_pow {n k : ℕ} (h : 2 * k + 1 ≤ n) :
    ((1 - X : ℤ[X]) ^ n).coeff (2 * k + 1) = -(n.choose (2 * k + 1) : ℤ) := by
  have heq : (1 - X : ℤ[X]) = C (-1) * (X + C (-1)) := by simp; ring
  rw [heq, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow, ← mul_assoc, ← pow_add,
    show n + (n - (2 * k + 1)) = 2 * ((n - (2 * k + 1)) + k) + 1 by omega, pow_succ, pow_mul]
  norm_num

private theorem coeff_binomialPolynomial (m k : ℕ) :
    (binomialPolynomial (X - 1) m).coeff k =
      ∑ i ∈ Icc k (m / 2), (-1) ^ (i - k) * weightedChoose m i * (i.choose k : ℤ) := by
  rw [show (X - 1 : ℤ[X]) = X + C (-1) by simp [sub_eq_add_neg], binomialPolynomial,
    ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul, coeff_X_add_C_pow]
  have hsubset : Icc k (m / 2) ⊆ range (m + 1) := by
    intro i hi
    have := mem_Icc.mp hi
    exact mem_range.mpr (by omega)
  calc
    _ = ∑ i ∈ Icc k (m / 2), weightedChoose m i * ((-1) ^ (i - k) * (i.choose k : ℤ)) := by
      symm
      refine sum_subset hsubset ?_
      intro i _ hi
      by_cases hik : i < k
      · simp [Nat.choose_eq_zero_of_lt hik]
      · have hm : m < 2 * i := by
          simp only [mem_Icc, not_and_or, not_le] at hi
          omega
        simp [weightedChoose_eq_zero hm]
    _ = _ := by
      apply sum_congr rfl
      intro i _
      ring

/-- **Binomial coefficients of odd lower index as an alternating sum.** For natural numbers $n$
and $k$ with $k < \lfloor (n-1)/2 \rfloor$,
$$\binom{n}{2k+1} = \sum_{i=k}^{\lfloor (n-1)/2 \rfloor} (-1)^{i-k} \, 2^{n-2i-1}
  \binom{n-i-1}{i} \binom{i}{k}.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (2) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem choose_two_mul_add_one_eq_alternating_sum {n k : ℕ}
    (hk : k < (n - 1) / 2) :
    (n.choose (2 * k + 1) : ℤ) =
      ∑ i ∈ Icc k ((n - 1) / 2),
        (-1) ^ (i - k) * 2 ^ (n - 2 * i - 1) * ((n - i - 1).choose i : ℤ) * (i.choose k : ℤ) := by
  cases n with
  | zero => omega
  | succ m =>
    have hExpand : expand ℤ 2 (binomialPolynomial (X - 1) m) =
        binomialPolynomial (X ^ 2 - 1) m := by
      simp [binomialPolynomial, expand_X]
    apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
    calc
      _ = ((1 + X : ℤ[X]) ^ (m + 1) - (1 - X) ^ (m + 1)).coeff (2 * k + 1) := by
        rw [coeff_sub, coeff_one_add_X_pow, coeff_one_sub_X_pow (by omega)]
        ring
      _ = 2 * (binomialPolynomial (X - 1) m).coeff k := by
        rw [pow_sub_eq, ← hExpand, mul_right_comm, coeff_mul_X, ← C_ofNat, coeff_C_mul,
          coeff_expand_mul' (by decide : 0 < 2)]
      _ = _ := by
        rw [coeff_binomialPolynomial, Nat.succ_sub_one]
        congr 1
        apply sum_congr rfl
        intro i _
        simp only [weightedChoose, show m + 1 - 2 * i - 1 = m - 2 * i by omega,
          show m + 1 - i - 1 = m - i by omega]
        ring

end MetaMathlibExt

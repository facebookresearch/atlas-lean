/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.StirlingAscPochhammer

/-!
# Lee's identity for Stirling numbers of the first kind from smaller rows

We prove the recurrence simultaneously for all columns using the rising factorial
polynomials. Pascal's rule on the sum side matches the product rule on the
polynomial side.

Reference: Kwankyu Lee, *Some New Identities for Stirling Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.2.7, Theorem 11
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Lee/lee14.html>).
-/

open Finset Polynomial

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

-- The sum for row `n + 1`, with the summation index shifted down by two.
private noncomputable def smallerRowsSum (n : ℕ) : ℤ[X] :=
  ∑ i ∈ range n, ((n + 1).choose (i + 2) : ℤ[X]) * (i.factorial : ℤ[X]) *
    ascPochhammer ℤ (n - i)

private theorem smallerRowsSum_succ (n : ℕ) :
    smallerRowsSum (n + 1) = smallerRowsSum n * (X + (↑(n + 1) : ℤ[X])) +
      (↑(n + 1) : ℤ[X]) * ascPochhammer ℤ (n + 1) := by
  let f (i : ℕ) : ℤ[X] :=
    ((n + 1).choose (i + 2) : ℤ[X]) * (i.factorial : ℤ[X]) * ascPochhammer ℤ (n + 1 - i)
  let g (i : ℕ) : ℤ[X] :=
    ((n + 1).choose (i + 1) : ℤ[X]) * (i.factorial : ℤ[X]) * ascPochhammer ℤ (n + 1 - i)
  have hpascal : smallerRowsSum (n + 1) = ∑ i ∈ range (n + 1), (f i + g i) := by
    unfold smallerRowsSum
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [f, g, Nat.choose_succ_succ' (n + 1) (i + 1), Nat.cast_add, add_mul]
    exact add_comm _ _
  have hf : f n = 0 := by
    simp [f]
  have hg : g 0 = (↑(n + 1) : ℤ[X]) * ascPochhammer ℤ (n + 1) := by
    simp [g]
  -- The unshifted part ends in zero; the shifted part starts with `(n + 1) * P_(n + 1)`.
  rw [hpascal, sum_add_distrib, sum_range_succ f, hf, add_zero, sum_range_succ' g, hg,
    ← add_assoc, ← sum_add_distrib, smallerRowsSum, sum_mul]
  congr 1
  refine sum_congr rfl fun i hi ↦ ?_
  have hin := mem_range.mp hi
  have hrow : n + 1 - i = (n - i) + 1 := by omega
  have hcast : (↑(n - i) : ℤ[X]) + ↑(i + 1) = ↑(n + 1) := by
    rw [← Nat.cast_add, show n - i + (i + 1) = n + 1 by omega]
  simp only [f, g, hrow, Nat.add_sub_add_right, ascPochhammer_succ_right ℤ (n - i),
    Nat.factorial_succ i, Nat.cast_mul, ← hcast]
  ring

private theorem ascPochhammer_sub_X_mul_derivative (n : ℕ) :
    (↑(n + 1) : ℤ[X]) * ascPochhammer ℤ (n + 1) -
      X * derivative (ascPochhammer ℤ (n + 1)) = smallerRowsSum n := by
  induction n with
  | zero => simp [ascPochhammer_succ_right, smallerRowsSum]
  | succ n ih =>
    rw [smallerRowsSum_succ, ← ih, ascPochhammer_succ_right ℤ (n + 1), derivative_mul]
    simp only [map_add, derivative_X, derivative_natCast, add_zero, mul_one]
    simp only [Nat.cast_succ]
    ring

private theorem ascPochhammer_coeff (n k : ℕ) :
    (ascPochhammer ℤ n).coeff k = (Nat.stirlingFirst n k : ℤ) := by
  rw [← Nat.sum_stirlingFirst_mul_X_pow, finsetSum_coeff]
  by_cases hk : k ≤ n
  · simp [coeff_X_pow, mul_ite, hk]
  · rw [Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_of_not_ge hk), Nat.cast_zero]
    apply sum_eq_zero
    intro i hi
    have hik : k ≠ i := by have := mem_range.mp hi; omega
    simp [coeff_X_pow, hik]

/-- **Lee's identity for Stirling numbers of the first kind from smaller rows.** Write $c(n, k)$
for the unsigned Stirling number of the first kind, the number of permutations of $n$ elements
with exactly $k$ cycles. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$, the
following identity of integers holds:
$$(n - k)\, c(n, k) = \sum_{j=2}^{n-k+1} \binom{n}{j}\, (j-2)!\, c(n-j+1, k).$$

This is Lee's Theorem 11 with the denominator $n - k$ cleared.

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 11
(TeX label `thm:mdkda`). -/
public theorem stirlingFirst_mul_sub_eq_sum_choose_factorial
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ((n : ℤ) - k) * (Nat.stirlingFirst n k : ℤ) =
      ∑ j ∈ Finset.Icc 2 (n - k + 1),
        (Nat.choose n j : ℤ) * (Nat.stirlingFirst (n - j + 1) k : ℤ) *
          (Nat.factorial (j - 2) : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  let term (j : ℕ) : ℤ :=
    ((m + 1).choose j : ℤ) * Nat.stirlingFirst (m + 1 - j + 1) (l + 1) * (j - 2).factorial
  change _ = ∑ j ∈ Icc 2 (m + 1 - (l + 1) + 1), term j
  have hcoeff := congrArg (fun p : ℤ[X] ↦ p.coeff (l + 1))
    (ascPochhammer_sub_X_mul_derivative m)
  simp only [coeff_sub, ← C_eq_natCast, coeff_C_mul, coeff_X_mul, coeff_derivative,
    ascPochhammer_coeff, smallerRowsSum, finsetSum_coeff, ← C_mul] at hcoeff
  calc
    _ = ∑ i ∈ range m, ((m + 1).choose (i + 2) : ℤ) * (i.factorial : ℤ) *
          Nat.stirlingFirst (m - i) (l + 1) := by
      rw [← hcoeff]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = ∑ j ∈ Icc 2 (m + 1), term j := by
      rw [← Ico_add_one_right_eq_Icc, show m + 1 + 1 = m + 2 by rfl,
        ← sum_Ico_add' term 0 m 2, Nat.Ico_zero_eq_range]
      refine sum_congr rfl fun i hi ↦ ?_
      have := mem_range.mp hi
      simp only [term, show m + 1 - (i + 2) + 1 = m - i by omega, Nat.add_sub_cancel]
      ring
    _ = _ := by
      symm
      apply sum_subset
      · intro j hj
        simp only [mem_Icc] at hj ⊢
        omega
      · intro j hj hout
        simp only [mem_Icc] at hj hout
        simp [term, Nat.stirlingFirst_eq_zero_of_lt (show m + 1 - j + 1 < l + 1 by omega)]

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

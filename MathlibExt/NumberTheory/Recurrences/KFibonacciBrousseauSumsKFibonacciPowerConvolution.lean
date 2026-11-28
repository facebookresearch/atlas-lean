/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.Recurrences.FibonacciBrousseauSums
public import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSums
public import MathlibExt.NumberTheory.Recurrences.PellBrousseauOdd
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.Internal.BrousseauSum

/-!
# Power-weighted convolution of k-Fibonacci numbers

We prove the endpoint formula for the power-weighted convolution of k-Fibonacci numbers.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 4 (`jis-2024-24.6.4-thm-4`).
-/

namespace MetaMathlibExt

open Finset

private lemma coeff_reflect (k : ℚ) (p : ℕ) (x : ℚ) :
    (-1 : ℚ) ^ p * brousseauCoeff k p (-x) =
      ∑ r ∈ range (p + 1), brousseauA k r * (p.choose r : ℚ) * x ^ (p - r) := by
  rw [brousseauCoeff, mul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  have hr' : r ≤ p := Nat.le_of_lt_succ (mem_range.mp hr)
  have hsign : (-1 : ℚ) ^ p * (-1) ^ r * (-1) ^ (p - r) = 1 := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hr', ← mul_pow]
    norm_num
  rw [neg_eq_neg_one_mul x, mul_pow]
  linear_combination brousseauA k r * (p.choose r : ℚ) * x ^ (p - r) * hsign

@[expose] public section

/-- **Power-weighted convolution of k-Fibonacci numbers.** Let $k$ be a nonzero integer and let
$F_{k,n}$ be the $k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$: $F_{k,0} = 0$,
$F_{k,1} = 1$ and $F_{k,n+2} = k F_{k,n+1} + F_{k,n}$. Let $A_k^{(0)} = 1$ and
$A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)}$ for
$p \ge 1$. Then for all natural numbers $n$ and $p$, with $0^0 = 1$,
$$
k \sum_{i=0}^{n} i^p F_{k,n-i} = A_k^{(p)} F_{k,n+1} +
\sum_{r=0}^{p} A_k^{(r)} \binom{p}{r} \left((-1)^{p-r} F_{k,n} - n^{p-r}\right).
$$

The source takes $k$ to be a positive integer.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 4 (`jis-2024-24.6.4-thm-4`). -/
public theorem kFibonacci_power_convolution (k : ℤ) (hk : k ≠ 0) (n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ (n - i) =
      brousseauA k p * lucasU ⟨k, -1, by decide⟩ (n + 1) +
        ∑ r ∈ Finset.range (p + 1), brousseauA k r * (p.choose r : ℚ) *
          ((-1) ^ (p - r) * lucasU ⟨k, -1, by decide⟩ n - (n : ℚ) ^ (p - r)) := by
  let U (i : ℕ) : ℚ := lucasU ⟨k, -1, by decide⟩ i
  let D (x : ℚ) := (-1 : ℚ) ^ p * brousseauCoeff k p (-x)
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have shift (x : ℚ) :
      (k : ℚ) * D x + D (x - 1) - D (x + 1) = (k : ℚ) * x ^ p := by
    have h := BrousseauSum.coeff_shift (k : ℚ) hk' p (-x)
    have hsign : (-1 : ℚ) ^ p * (-x) ^ p = x ^ p := by
      rw [neg_eq_neg_one_mul x, mul_pow, ← mul_assoc, ← mul_pow]
      norm_num
    have hminus : -(x - 1) = -x + 1 := by ring
    have hplus : -(x + 1) = -x - 1 := by ring
    simp only [D, hminus, hplus]
    linear_combination (-1 : ℚ) ^ p * h + (k : ℚ) * hsign
  have zero : D 0 = brousseauA k p := by
    change (-1 : ℚ) ^ p * brousseauCoeff k p (-0) = brousseauA k p
    rw [coeff_reflect, sum_range_succ, sum_eq_zero]
    · simp
    · intro r hr
      rw [zero_pow (by have := mem_range.mp hr; omega), mul_zero]
  let T (i : ℕ) := D i * U (n + 1 - i) + D ((i : ℚ) - 1) * U (n - i)
  have step (i : ℕ) (hi : i < n) :
      (k : ℚ) * ((i : ℚ) ^ p * U (n - i)) = T i - T (i + 1) := by
    have recurrence : U (n + 1 - i) = (k : ℚ) * U (n - i) + U (n - (i + 1)) := by
      have h := lucasU_add_two ⟨k, -1, by decide⟩ (n - (i + 1))
      simp only [neg_one_mul, sub_neg_eq_add,
        show n - (i + 1) + 2 = n + 1 - i by omega,
        show n - (i + 1) + 1 = n - i by omega] at h
      dsimp only [U]
      exact_mod_cast h
    have hD := shift (i : ℚ)
    simp only [T, Nat.cast_add_one, add_sub_cancel_right,
      show n + 1 - (i + 1) = n - i by omega]
    rw [recurrence]
    linear_combination -U (n - i) * hD
  have telescoped :
      (k : ℚ) * ∑ i ∈ range (n + 1), (i : ℚ) ^ p * U (n - i) =
        brousseauA k p * U (n + 1) + D (-1) * U n - D n := by
    rw [sum_range_succ]
    simp only [Nat.sub_self, show U 0 = 0 by simp [U, lucasU], mul_zero, add_zero]
    rw [mul_sum, sum_congr rfl (fun i hi ↦ step i (mem_range.mp hi)), sum_range_sub']
    simp [T, zero, U, lucasU]
  change (k : ℚ) * ∑ i ∈ range (n + 1), (i : ℚ) ^ p * U (n - i) =
    brousseauA k p * U (n + 1) + ∑ r ∈ range (p + 1),
      brousseauA k r * (p.choose r : ℚ) * ((-1) ^ (p - r) * U n - (n : ℚ) ^ (p - r))
  rw [telescoped]
  simp only [D, coeff_reflect, sum_mul]
  rw [add_sub_assoc, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun r _ ↦ ?_
  ring

end

end MetaMathlibExt

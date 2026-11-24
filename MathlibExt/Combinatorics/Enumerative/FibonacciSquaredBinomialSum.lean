/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Ring

/-!
# Squared Fibonacci numbers as a double binomial sum

`fib_succ_sq_eq_sum_choose_mul_choose` expresses a Fibonacci square as a sum of Delannoy
numbers along the line `3 * i + k = 2 * n`, with each Delannoy number given by a binomial sum.
-/

namespace MetaMathlibExt

open Finset

namespace fib_succ_sq_eq_sum_choose_mul_choose

private def binomialSum (i k : ℕ) : ℕ :=
  ∑ j ∈ range (i + 1), i.choose j * k.choose j * 2 ^ j

-- Pascal's identity in the first binomial coefficient gives a sum with shifted second index.
private theorem binomialSum_succ (i k : ℕ) :
    binomialSum (i + 1) k = binomialSum i k +
      ∑ j ∈ range (i + 1), i.choose j * k.choose (j + 1) * 2 ^ (j + 1) := by
  simpa only [binomialSum, Nat.cast_id, mul_assoc] using
    sum_choose_succ_mul (fun j _ => k.choose j * 2 ^ j) i

private theorem binomialSum_zero_left (k : ℕ) : binomialSum 0 k = 1 := by
  simp [binomialSum]

private theorem binomialSum_zero_right (i : ℕ) : binomialSum i 0 = 1 := by
  simp [binomialSum, sum_range_succ']

-- Pascal's identity in the second coefficient of the shifted sum gives the Delannoy recurrence.
private theorem binomialSum_succ_succ (i k : ℕ) :
    binomialSum (i + 1) (k + 1) = binomialSum i (k + 1) + binomialSum (i + 1) k +
      binomialSum i k := by
  rw [binomialSum_succ i (k + 1), binomialSum_succ i k]
  simp only [Nat.choose_succ_succ, Nat.succ_eq_add_one, add_mul, mul_add, sum_add_distrib]
  have h : (∑ j ∈ range (i + 1), i.choose j * k.choose j * 2 ^ (j + 1)) =
      binomialSum i k + binomialSum i k := by
    simp [binomialSum, ← sum_add_distrib, pow_succ, Nat.mul_two, mul_add]
  omega

-- Outside the line segment in the first quadrant there is no contribution.
private def entry (m i : ℕ) : ℕ :=
  if 3 * i ≤ m then binomialSum i (m - 3 * i) else 0

private theorem entry_succ (m i : ℕ) :
    entry (m + 4) (i + 1) = entry (m + 3) (i + 1) + entry (m + 1) i + entry m i := by
  by_cases h : 3 * i ≤ m
  · simp (disch := omega) only [entry, ite_eq_left]
    rw [show m + 4 - 3 * (i + 1) = (m - 3 * i) + 1 by omega, binomialSum_succ_succ,
      show m + 3 - 3 * (i + 1) = m - 3 * i by omega,
      show m + 1 - 3 * i = (m - 3 * i) + 1 by omega]
    omega
  · by_cases h' : 3 * i = m + 1
    · simp [entry, h', Nat.mul_add, binomialSum_zero_right]
    · simp (disch := omega) only [entry, ite_eq_right, Nat.zero_add]

private def diagonal (m : ℕ) : ℕ := ∑ i ∈ range (m / 3 + 1), entry m i

private theorem diagonal_eq_sum (m b : ℕ) (hb : m / 3 < b) :
    diagonal m = ∑ i ∈ range b, entry m i := by
  apply sum_subset (range_mono (by omega : m / 3 + 1 ≤ b))
  intro i _ hi
  simp only [mem_range] at hi
  exact ite_eq_right (by omega)

-- The three Delannoy predecessors have weights one, three, and four less.
private theorem diagonal_add_four (m : ℕ) :
    diagonal (m + 4) = diagonal (m + 3) + diagonal (m + 1) + diagonal m := by
  rw [diagonal_eq_sum (m + 4) (m + 4 + 1) (by omega),
    diagonal_eq_sum (m + 3) (m + 4 + 1) (by omega),
    diagonal_eq_sum (m + 1) (m + 4) (by omega), diagonal_eq_sum m (m + 4) (by omega)]
  simp only [sum_range_succ' (entry (m + 4)), sum_range_succ' (entry (m + 3)), entry_succ,
    sum_add_distrib]
  simp [entry, binomialSum_zero_left, add_comm, add_left_comm]

-- Adjacent even and odd diagonals give a square and a product of consecutive Fibonacci numbers.
private theorem diagonal_pair (n : ℕ) :
    diagonal (2 * n) = Nat.fib (n + 1) ^ 2 ∧
      diagonal (2 * n + 1) = Nat.fib (n + 1) * Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih₀ ih₁ =>
    have even := diagonal_add_four (2 * n)
    have odd := diagonal_add_four (2 * n + 1)
    rw [show 2 * n + 3 = 2 * (n + 1) + 1 by omega, ih₁.2, ih₀.2, ih₀.1] at even
    rw [show 2 * n + 1 + 3 = 2 * n + 4 by omega, even,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega, ih₁.1, ih₀.2] at odd
    rw [show 2 * (n + 2) = 2 * n + 4 by omega]
    constructor
    · rw [even, Nat.fib_add_two (n := n + 1)]
      ring
    · rw [show 2 * n + 4 + 1 = 2 * n + 1 + 4 by omega, odd,
        Nat.fib_add_two (n := n + 2), Nat.fib_add_two (n := n + 1)]
      ring

end fib_succ_sq_eq_sum_choose_mul_choose

open fib_succ_sq_eq_sum_choose_mul_choose in
/-- **Squared Fibonacci numbers as a double binomial sum.** Let $F_k$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$). For every natural number $n$,
$$
F_{n+1}^2 = \sum_{i=0}^{\lfloor 2n/3 \rfloor} \sum_{j=0}^{i} \binom{i}{j} \binom{2n-3i}{j} 2^j.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.3 (`fq-2024-belaggoun01132024-cor-3.3`). -/
public theorem fib_succ_sq_eq_sum_choose_mul_choose (n : ℕ) :
    Nat.fib (n + 1) ^ 2 =
      ∑ i ∈ range (2 * n / 3 + 1), ∑ j ∈ range (i + 1),
        i.choose j * (2 * n - 3 * i).choose j * 2 ^ j := by
  rw [← (diagonal_pair n).1]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [entry, ite_eq_left (by omega)]
  rfl

end MetaMathlibExt

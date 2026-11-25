/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BinomialSumRecurrences
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- Both orders are zero; the lower bound on `N` uses truncated subtraction.
example (x A a : ℕ → ℤ) (hx : ∀ n, x n = 0) :
    x 5 = ∑ i ∈ Finset.Icc 1 0, a i * x (5 - i) := by
  apply linearRecurrence_of_finite_window x A a 0 0 0
  · intro n _
    simp [hx]
  · decide
  · intro n _ _
    simp [hx]
  · decide

-- The initial window is empty when `r = 0`, `s = 2`, and `N = 1`.
example (x A a : ℕ → ℤ) (hx : ∀ n, x n = 0) :
    x 5 = ∑ i ∈ Finset.Icc 1 2, a i * x (5 - i) := by
  apply linearRecurrence_of_finite_window x A a 0 2 1
  · intro n _
    simp [hx]
  · decide
  · intro n hsn hn
    omega
  · decide

-- With `s = 0`, the window gives exactly the initial zero values for `hA`.
example (x A : ℕ → ℤ)
    (hA : ∀ n, 2 ≤ n → x n = ∑ i ∈ Finset.Icc 1 2, A i * x (n - i))
    (h₀ : x 0 = 0) (h₁ : x 1 = 0) : x 5 = 0 := by
  have h := linearRecurrence_of_finite_window x A (fun _ ↦ 0) 2 0 1 hA (by decide)
    (by
      intro n _ hn
      interval_cases n <;> simp [h₀, h₁]) 5 (by decide)
  simpa using h

-- The integer sequence `x n = n` satisfies two different recurrences. Check
-- the second beyond the supplied window, which consists of 3 and 4.
example (n : ℕ) (hn : 4 < n) :
    (n : ℤ) = ∑ i ∈ Finset.Icc 1 3, (if i ≤ 2 then 1 else -1) * (↑(n - i) : ℤ) := by
  let x : ℕ → ℤ := fun n ↦ n
  let A : ℕ → ℤ := fun i ↦ if i = 1 then 2 else -1
  let a : ℕ → ℤ := fun i ↦ if i ≤ 2 then 1 else -1
  have hA (n : ℕ) (hn : 2 ≤ n) : x n = ∑ i ∈ Finset.Icc 1 2, A i * x (n - i) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide]
    simp [x, A, Finset.sum_insert, Int.ofNat_sub (show 1 ≤ n by omega), Int.ofNat_sub hn]
    omega
  have ha (n : ℕ) (hs : 3 ≤ n) (hn : n ≤ 4) :
      x n = ∑ i ∈ Finset.Icc 1 3, a i * x (n - i) := by
    interval_cases n <;> decide
  exact linearRecurrence_of_finite_window x A a 2 3 4 hA (by decide) ha n (by omega)

open PowerSeries

local notation "Xq" => (X : PowerSeries ℚ)

-- For the identity Riordan array, the two residues modulo two select separate monomials.
example : coeff 4 ((1 - Xq ^ 2)⁻¹) = 1 := by
  have h := riordan_stepSum_coeff (1 : PowerSeries ℚ) Xq (by simp) 2 0
    (by decide) (by decide) 4
  simp only [Nat.add_zero, pow_zero, one_mul, mul_one] at h
  rw [← h]
  norm_num [Finset.sum_range_succ, coeff_X_pow]
  decide

example : coeff 3 (Xq * (1 - Xq ^ 2)⁻¹) = 1 := by
  have h := riordan_stepSum_coeff (1 : PowerSeries ℚ) Xq (by simp) 2 1
    (by decide) (by decide) 3
  simp only [pow_one, one_mul] at h
  rw [← h]
  norm_num [Finset.sum_range_succ, coeff_X_pow]

example : coeff 0 (Xq * (1 - Xq ^ 2)⁻¹) = 0 := by
  have h := riordan_stepSum_coeff (1 : PowerSeries ℚ) Xq (by simp) 2 1
    (by decide) (by decide) 0
  simp only [pow_one, one_mul] at h
  rw [← h]
  norm_num [Finset.sum_range_succ, coeff_X_pow]

section RationalRiordan

local notation "Xz" => (Polynomial.X : Polynomial ℤ)

-- Pascal's triangle `g = 1 / (1 - x)`, `h = x / (1 - x)` with step `3`: the sums of the binomial
-- coefficients `C(n, 3j + p)` for `p = 0, 1, 2` share one recurrence.
example := rationalRiordan_stepSum_linearRecurrence 1 (1 - Xz) 1 (1 - Xz) 1 (by simp) (by simp)
  (by simp) le_rfl 3 (by decide)

-- Step `1` (whole rows), which `riordan_stepSum_coeff` excludes, with `ν = 2`.
example := rationalRiordan_stepSum_linearRecurrence (1 + Xz) 1 (1 + 2 * Xz) (1 - Xz - Xz ^ 2) 2
  (by simp) (by simp) (by simp) (by decide) 1 one_pos

-- For `g = 1` and `h = x` with step `1`, every step sum is `1`, so the coefficients of the
-- recurrence sum to `1`.
example : ∃ (r : ℕ) (αs : ℕ → ℤ), ∑ i ∈ Finset.Icc 1 r, αs i = 1 := by
  obtain ⟨r, αs, H⟩ := rationalRiordan_stepSum_linearRecurrence 1 1 1 1 1 (by simp) (by simp)
    (by simp) le_rfl 1 one_pos
  refine ⟨r, αs, ?_⟩
  have := H 0 one_pos r le_rfl
  simp [coeff_X_pow] at this
  exact_mod_cast this.symm

end RationalRiordan

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SabarTriangle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.SabarTriangle` -/

namespace MathlibExtTest.SabarTriangle

open MetaMathlibExt

/-- The left side of the reciprocal binomial sum identity. -/
private def lhs (n : ℕ) : ℚ :=
  (1 / ((n + 1 : ℕ) : ℚ)) * ∑ i ∈ Finset.range (n + 1), 1 / (n.choose i : ℚ)

/-- The right side of the reciprocal binomial sum identity. -/
private def rhs (n : ℕ) : ℚ :=
  1 + ∑ i ∈ Finset.range (n - 1),
    (-1 : ℚ) ^ (n - i - 1) * sabarNumber (n - 1) i / (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ))

-- The theorem's statement is `lhs n = rhs n`.
private theorem lhs_eq_rhs (n : ℕ) (hn : 2 ≤ n) : lhs n = rhs n :=
  sum_inv_choose_succ_eq_one_add_sum_sabarNumber n hn

-- The convention: `s(n, i)` is the empty sum `0` for `i ≥ n`.
example (n i : ℕ) (h : n ≤ i) : sabarNumber n i = 0 := by
  simp [sabarNumber, Finset.Ioc_eq_empty_of_le h]

-- The rows that enter the identity for `n ≤ 4`.
example : sabarNumber 1 0 = 1 ∧ (List.range 2).map (sabarNumber 2) = [0, 2] ∧
    (List.range 3).map (sabarNumber 3) = [1, 1, 3] := by
  decide +kernel

-- Consecutive entries in column 2, starting with the empty diagonal entry at `d = 0`.
example : ∀ d ∈ Finset.range 5,
    sabarNumber (2 + d + 1) 2 = ((2 + d + 1).choose 2 : ℤ) - sabarNumber (2 + d) 2 := by
  decide +kernel

-- At `n = 2` both sides are `5 / 6`. With the opposite sign `(-1)^(n-i)` (the printed sign, per
-- the theorem's docstring), the right side would be `1 + s(1, 0) / (2 * 3) = 7 / 6` instead.
example : lhs 2 = 5 / 6 ∧ rhs 2 = 5 / 6 := by
  refine ⟨?_, ?_⟩
  · norm_num [lhs, Finset.sum_range_succ]
  · rw [← lhs_eq_rhs 2 le_rfl]
    norm_num [lhs, Finset.sum_range_succ]

example : 1 + ∑ i ∈ Finset.range (2 - 1),
    (-1 : ℚ) ^ (2 - i) * sabarNumber (2 - 1) i / (((2 - i : ℕ) : ℚ) * ((2 + 1 - i : ℕ) : ℚ)) =
      7 / 6 := by
  have h : sabarNumber 1 0 = 1 := by decide +kernel
  norm_num [Finset.sum_range_succ, h]

-- The theorem evaluates the alternating sum of row `3` of Sabar's triangle: at `n = 4` the right
-- side is `1 - 1 / 20 + 1 / 12 - 3 / 6 = 8 / 15`, the mean `(1 + 1/4 + 1/6 + 1/4 + 1) / 5`.
example : rhs 4 = 8 / 15 := by
  rw [← lhs_eq_rhs 4 (by norm_num)]
  norm_num [lhs, Finset.sum_range_succ, Nat.choose]

-- An independent check by evaluation for `2 ≤ n ≤ 7`.
example : ∀ n ∈ Finset.Icc 2 7, lhs n = rhs n := by
  decide +kernel

example (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range (2 * n - 1), (-1 : ℚ) ^ i * sabarNumber (2 * n - 1) i / ((i + 1 : ℕ) : ℚ) =
      harmonic n :=
  sum_sabarNumber_div_succ_eq_harmonic (n := n) (hn := hn)

-- Both sides of the harmonic identity, evaluated independently in the rationals.
example : (∑ i ∈ Finset.range (2 * 2 - 1),
    (-1 : ℚ) ^ i * sabarNumber (2 * 2 - 1) i / ((i + 1 : ℕ) : ℚ)) = 3 / 2 ∧
    harmonic 2 = 3 / 2 := by
  decide +kernel

example : (∑ i ∈ Finset.range (2 * 3 - 1),
    (-1 : ℚ) ^ i * sabarNumber (2 * 3 - 1) i / ((i + 1 : ℕ) : ℚ)) = 11 / 6 ∧
    harmonic 3 = 11 / 6 := by
  decide +kernel

-- The declared formula, also evaluated directly on both sides through index seven.
private def centralWhittRhs (n : ℕ) : ℚ :=
  (2 / 3) * ((2 * n).choose n : ℚ) - (1 / 3) * whittGeneralizedCatalan 2 n / 2 ^ (n + 1) +
    (-1) ^ (n + 1) + (-1) ^ n / 2 ^ (n + 1)

example (n : ℕ) (hn : 1 ≤ n) : (sabarNumber (2 * n) n : ℚ) = centralWhittRhs n :=
  sabarNumber_central_eq_whittGeneralizedCatalan n hn

-- This includes the lower endpoint and both parities of the correction term.
example : ∀ n ∈ Finset.Icc 1 7, (sabarNumber (2 * n) n : ℚ) = centralWhittRhs n := by
  decide +kernel

-- Check the three even-row formulas and the odd-row formula by evaluating both sides.
private def centralFineRhs (n : ℕ) : ℚ × ℚ × ℚ × ℚ :=
  ⟨(1 / 6) * ((2 * n + 2).choose (n + 1) : ℚ) + (2 / 3) * fineNumber n + (-1) ^ (n + 1),
    (1 / 3) * (2 * n + 1) * (catalan n : ℚ) + (2 / 3) * fineNumber n + (-1) ^ (n + 1),
    (2 / 3) * ((2 * n).choose n : ℚ) - (1 / 3) * fineNumber (n - 1) + (-1) ^ (n + 1),
    (2 / 3) * ((2 * n - 1).choose n : ℚ) + (1 / 3) * fineNumber (n - 1) + (-1) ^ n⟩

private def centralEntries (n : ℕ) : ℚ × ℚ × ℚ × ℚ :=
  ⟨sabarNumber (2 * n) n, sabarNumber (2 * n) n, sabarNumber (2 * n) n,
    sabarNumber (2 * n - 1) n⟩

example (n : ℕ) (hn : 1 ≤ n) : centralEntries n = centralFineRhs n := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := sabarNumber_central_eq_fineNumber n hn
  exact Prod.ext h₁ (Prod.ext h₂ (Prod.ext h₃ h₄))

-- At `n = 1` the odd entry is the empty sum; `n = 2, 3` test both signs above the endpoint.
example : ∀ n ∈ Finset.Icc 1 7, centralEntries n = centralFineRhs n := by
  decide +kernel

end MathlibExtTest.SabarTriangle

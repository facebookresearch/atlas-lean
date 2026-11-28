/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PalindromeAPCountBaseMinusOne

open MetaMathlibExt

-- Check the one-digit boundary at modulus one and at an even modulus.
example : palindromeAPCount 2 1 1 0 = 1 ∧ palindromeAPCount 5 4 4 0 = 1 := by
  decide +kernel

-- Count independently on either side of a reflected cutoff that has residue zero.
example : palindromeAPCount 5 87 4 0 = 6 ∧ palindromeAPCount 5 88 4 0 = 7 := by
  decide +kernel

-- The remaining parity branches, counted directly from the digits rather than the formula.
example : palindromeAPCount 4 38 3 2 = 5 ∧ palindromeAPCount 5 17 4 1 = 1 ∧
    palindromeAPCount 5 17 4 2 = 2 ∧ palindromeAPCount 5 88 4 3 = 4 := by
  decide +kernel

-- Apply the formula to the same one-digit inputs and compare with the direct counts above.
example : (palindromeAPCount 2 1 1 0 : ℚ) = 1 ∧ (palindromeAPCount 5 4 4 0 : ℚ) = 1 := by
  have hone := (palindromeAPCount_of_modEq_one (b := 2) (m := 1) (q := 1) (r := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1 (by decide)
  have heven := (palindromeAPCount_of_modEq_one (b := 5) (m := 4) (q := 4) (r := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  have hd₁ : Nat.digits 2 1 = [1] := by decide
  have hd₄ : Nat.digits 5 4 = [4] := by decide
  have hc₁ : palindromicHalfCopy 2 1 ≤ 1 := by decide
  have hc₄ : palindromicHalfCopy 5 4 ≤ 4 := by decide
  norm_num [hd₁, hd₄, hc₁, hc₄, Nat.odd_iff, Nat.even_iff, Finset.sum_range_succ] at hone heven ⊢
  exact ⟨hone, heven⟩

-- Just below the reflected cutoff the formula excludes it; at the cutoff it contributes one.
example : (palindromeAPCount 5 87 4 0 : ℚ) = 6 ∧ (palindromeAPCount 5 88 4 0 : ℚ) = 7 := by
  have hbelow := (palindromeAPCount_of_modEq_one (b := 5) (m := 87) (q := 4) (r := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  have hat := (palindromeAPCount_of_modEq_one (b := 5) (m := 88) (q := 4) (r := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  have hd₈₇ : Nat.digits 5 87 = [2, 2, 3] := by decide
  have hd₈₈ : Nat.digits 5 88 = [3, 2, 3] := by decide
  have hc₈₇ : ¬ palindromicHalfCopy 5 87 ≤ 87 := by decide
  have hc₈₈ : palindromicHalfCopy 5 88 ≤ 88 := by decide
  norm_num [hd₈₇, hd₈₈, hc₈₇, hc₈₈, Nat.odd_iff, Nat.even_iff, Finset.sum_range_succ] at hbelow hat
  exact ⟨hbelow, hat⟩

-- With odd modulus and two digits, the reflected endpoint `22` in base four enters at 10.
example : palindromeAPCount 4 9 3 1 = 1 ∧ palindromeAPCount 4 10 3 1 = 2 := by
  decide +kernel

example : (palindromeAPCount 4 9 3 1 : ℚ) = 1 ∧ (palindromeAPCount 4 10 3 1 : ℚ) = 2 := by
  have hbelow := (palindromeAPCount_of_modEq_one (b := 4) (m := 9) (q := 3) (r := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1 (by decide)
  have hat := (palindromeAPCount_of_modEq_one (b := 4) (m := 10) (q := 3) (r := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1 (by decide)
  have hd₉ : Nat.digits 4 9 = [1, 2] := by decide
  have hd₁₀ : Nat.digits 4 10 = [2, 2] := by decide
  have hc₉ : ¬ palindromicHalfCopy 4 9 ≤ 9 := by decide
  have hc₁₀ : palindromicHalfCopy 4 10 ≤ 10 := by decide
  norm_num [hd₉, hd₁₀, hc₉, hc₁₀, Nat.even_iff, Finset.sum_range_succ] at hbelow hat ⊢
  exact ⟨hbelow, hat⟩

-- Odd modulus, with a center and an included endpoint.
example : (palindromeAPCount 4 38 3 2 : ℚ) = 5 := by
  have h := (palindromeAPCount_of_modEq_one (b := 4) (m := 38) (q := 3) (r := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1 (by decide)
  have hd : Nat.digits 4 38 = [2, 1, 2] := by decide
  have hc : palindromicHalfCopy 4 38 ≤ 38 := by decide
  norm_num [hd, hc, Nat.even_iff, Finset.sum_range_succ] at h
  exact h

-- With even digit length and even modulus, an odd residue can only occur at a shorter length.
example : (palindromeAPCount 5 17 4 1 : ℚ) = 1 := by
  have h := (palindromeAPCount_of_modEq_one (b := 5) (m := 17) (q := 4) (r := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  have hd : Nat.digits 5 17 = [2, 3] := by decide
  norm_num [hd, Nat.odd_iff] at h ⊢
  exact h

-- An even residue can occur at even digit length; here the reflected endpoint is too large.
example : (palindromeAPCount 5 17 4 2 : ℚ) = 2 := by
  have h := (palindromeAPCount_of_modEq_one (b := 5) (m := 17) (q := 4) (r := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  have hd : Nat.digits 5 17 = [2, 3] := by decide
  have hc : ¬ palindromicHalfCopy 5 17 ≤ 17 := by decide
  norm_num [hd, hc, Nat.odd_iff, Nat.even_iff, Finset.sum_range_succ] at h
  exact h

-- An odd residue at odd digit length uses the single center digit.
example : (palindromeAPCount 5 88 4 3 : ℚ) = 4 := by
  have h := (palindromeAPCount_of_modEq_one (b := 5) (m := 88) (q := 4) (r := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  have hd : Nat.digits 5 88 = [3, 2, 3] := by decide
  have hc : palindromicHalfCopy 5 88 ≤ 88 := by decide
  norm_num [hd, hc, Nat.odd_iff, Nat.even_iff, Finset.sum_range_succ] at h
  exact h

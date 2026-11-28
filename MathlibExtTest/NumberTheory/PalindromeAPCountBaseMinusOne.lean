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

-- At odd digit length, check both center parities and the residue-zero correction.
example : (palindromeAPCount 5 88 4 3 : ℚ) = 4 ∧ (palindromeAPCount 5 88 4 0 : ℚ) = 7 := by
  have ho := (palindromeAPCount_of_modEq_one (b := 5) (m := 88) (q := 4) (r := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  have he := (palindromeAPCount_of_modEq_one (b := 5) (m := 88) (q := 4) (r := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  have hd : Nat.digits 5 88 = [3, 2, 3] := by decide
  have hc : palindromicHalfCopy 5 88 ≤ 88 := by decide
  norm_num [hd, hc, Nat.odd_iff, Nat.even_iff, Finset.sum_range_succ] at ho he
  exact ⟨ho, he⟩

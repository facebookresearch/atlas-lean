/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PalindromeAPCountBasePow

open MetaMathlibExt

-- At k = 1 the cutoff itself is excluded; only one-digit palindromes contribute.
example : palindromeAPCount 4 (4 ^ 1) 2 0 = 1 ∧ palindromeAPCount 4 (4 ^ 1) 2 1 = 2 := by
  decide +kernel

example : palindromeAPCount 4 (4 ^ 1) 3 0 = 1 ∧ palindromeAPCount 5 (5 ^ 1) 4 1 = 1 ∧
    palindromeAPCount 5 (5 ^ 1) 4 2 = 1 := by
  decide +kernel

-- The two hypotheses overlap at q = 1, and give the same one-digit answer.
example : (palindromeAPCount 2 (2 ^ 1) 1 0 : ℚ) = 1 := by
  have ⟨hd, ho⟩ := palindromeAPCount_base_pow (b := 2) (k := 1) (q := 1) (r := 0)
    (by decide) (by decide) (by decide) (by decide)
  have h := hd (by decide)
  have h' := ho (by decide)
  norm_num [Nat.odd_iff] at h h' ⊢
  exact h'

-- Count directly, independently of the closed forms.
example : palindromeAPCount 4 (4 ^ 2) 2 0 = 2 ∧ palindromeAPCount 4 (4 ^ 2) 2 1 = 4 := by
  decide +kernel

example : palindromeAPCount 4 (4 ^ 3) 3 2 = 6 := by
  decide +kernel

-- With even modulus, only odd-length palindromes can contribute to an odd residue.
example : palindromeAPCount 5 (5 ^ 2) 4 1 = 1 ∧ palindromeAPCount 5 (5 ^ 2) 4 2 = 3 ∧
    palindromeAPCount 5 (5 ^ 3) 4 1 = 5 ∧ palindromeAPCount 5 (5 ^ 3) 4 2 = 9 := by
  decide +kernel

-- Apply the public theorem to the even-modulus, nonzero even-residue case.
example : (palindromeAPCount 5 (5 ^ 3) 4 2 : ℚ) = 9 := by
  have h := (palindromeAPCount_base_pow (b := 5) (k := 3) (q := 4) (r := 2)
    (by decide) (by decide) (by decide) (by decide)).2 (by decide)
  norm_num [Nat.odd_iff] at h ⊢
  exact h

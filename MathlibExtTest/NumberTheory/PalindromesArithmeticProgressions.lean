/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PalindromesArithmeticProgressions

open MetaMathlibExt

-- Zero is excluded, even in the zero residue class.
example : palindromeAPCount 4 0 3 0 = 0 := by decide

-- The two-digit palindromes end at (33)₄, and the next palindrome is (101)₄.
example : palindromeAPCount 4 16 3 2 = 2 ∧ palindromeAPCount 4 17 3 2 = 3 := by decide

-- At (202)₄ a carry in the leading half changes both outer digits.
example : palindromeAPCount 4 33 3 1 = 3 ∧ palindromeAPCount 4 34 3 1 = 4 := by decide

example : palindromeAPCount 4 34 1 0 = 11 := by decide

-- Below the reflected cutoff 88, the two prefix counts include two copies of zero.
example : Nat.count (fun x => 2 * x ≡ 0 [MOD 4]) 5 = 3 ∧
    Nat.count (fun x => 2 * (x / 5) + x % 5 ≡ 0 [MOD 4]) 17 = 5 ∧
    palindromeAPCount 5 87 4 0 = 6 := by decide

example : palindromeAPCount 5 87 4 0 + 2 = 8 := by
  have hd : (Nat.digits 5 87).length = 2 + 1 := by decide
  have h := palindromeAPCount_eq_prefix_counts (b := 5) (m := 87) (q := 4) (r := 0)
    (by decide) hd (by decide) (by decide)
  exact h.trans (by decide)

-- Inversion by two works for a nonzero residue modulo an odd modulus.
example : 2 * 4 ≡ 3 [MOD 5] ∧ 4 ≡ ((5 + 1) / 2) * 3 [MOD 5] := by decide

example : 4 ≡ ((5 + 1) / 2) * 3 [MOD 5] :=
  (Nat.two_mul_modEq_iff_of_odd (by decide : Odd 5) 4 3).mp (by decide)

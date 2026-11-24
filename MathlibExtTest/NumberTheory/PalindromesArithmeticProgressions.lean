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

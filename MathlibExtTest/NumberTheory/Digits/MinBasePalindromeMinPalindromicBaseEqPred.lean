/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.MinBasePalindromeMinPalindromicBaseEqPred
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.Digits.MinBasePalindromeMinPalindromicBaseEqPred` -/

namespace MathlibExtTest.NumberTheory.Digits.MinBasePalindromeMinPalindromicBaseEqPred

open MetaMathlibExt

-- The minimum palindromic base of `3` is `2`, since `3 = (1, 1)_2`.
theorem minPalindromicBase_three : minPalindromicBase 3 = 3 - 1 := by
  have h2mem : 2 ∈ {b | 2 ≤ b ∧ (Nat.digits b 3).Palindrome} := by
    refine ⟨by norm_num, ?_⟩
    rw [show Nat.digits 2 3 = [1, 1] by norm_num]
    exact List.Palindrome.of_reverse_eq rfl
  have hbase : minPalindromicBase 3 = 2 := by
    unfold minPalindromicBase
    apply le_antisymm (Nat.sInf_le h2mem)
    apply le_csInf ⟨2, h2mem⟩
    rintro b ⟨hb, -⟩
    exact hb
  rw [hbase]

-- `5` is an excluded small case: it is none of `3`, `4`, `6` and not greater than `6`, so
-- Brown's theorem rules out `b(5) = 5 - 1`.
example : minPalindromicBase 5 ≠ 5 - 1 := by
  intro h
  rcases minPalindromicBase_eq_pred 5 (by norm_num) h with h3 | h4 | h6eq | hgt
  · norm_num at h3
  · norm_num at h4
  · norm_num at h6eq
  · norm_num at hgt

-- `8` is composite and greater than `6`, so Brown's theorem rules out `b(8) = 8 - 1`.
example : minPalindromicBase 8 ≠ 8 - 1 := by
  intro h
  rcases minPalindromicBase_eq_pred 8 (by norm_num) h with h3 | h4 | h6eq | ⟨-, hp⟩
  · norm_num at h3
  · norm_num at h4
  · norm_num at h6eq
  · exact absurd hp (by decide)

-- Beyond `6`, a number whose minimum palindromic base is one less than itself is odd, since
-- Brown's theorem says it is prime and greater than `2`.
example (N : ℕ) (hN : 1 ≤ N) (h : minPalindromicBase N = N - 1) (h6 : 6 < N) :
    Odd N := by
  rcases minPalindromicBase_eq_pred N hN h with rfl | rfl | rfl | ⟨-, hp⟩
  · exact absurd h6 (by norm_num)
  · exact absurd h6 (by norm_num)
  · exact absurd h6 (by norm_num)
  · exact hp.odd_of_ne_two (by omega)

end MathlibExtTest.NumberTheory.Digits.MinBasePalindromeMinPalindromicBaseEqPred

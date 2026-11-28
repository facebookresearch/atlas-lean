/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PalindromeAPCountOfDvdBase

namespace MetaMathlibExt

-- For m = 322 in base five, the leading half is 32 and the reflection is 323.
example : palindromicHalfCopy 5 87 = 88 ∧ 87 / (5 : ℕ) = 17 := by decide +kernel

example : palindromicHalfCopy 5 87 = 88 ∧ 87 / (5 : ℕ) = 17 := by
  have hd : (Nat.digits 5 87).length = 2 + 1 := by decide
  have h := div_pow_half_eq_sum_digits (b := 5) (m := 87) (k := 2) (by decide) hd
  exact ⟨(palindromicHalfCopy_eq_ofDigits 5 87).trans (by decide), h.trans (by decide)⟩

-- In base six the bounds are 241 and 242. The final prefix contributes only at 242,
-- and only in the class of its leading digit, represented here by 5 modulo 3.
example : palindromeAPCount 6 97 3 0 = 2 ∧ palindromeAPCount 6 97 3 5 = 8 ∧
    palindromeAPCount 6 98 3 5 = 9 := by
  have below := palindromeAPCount_of_dvd_base (b := 6) (m := 97) (q := 3)
    (by decide) (by decide) (by decide) (by decide)
  have atCutoff := palindromeAPCount_of_dvd_base (b := 6) (m := 98) (q := 3)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨by exact_mod_cast below.1.trans (by decide +kernel : _ = (2 : ℚ)),
    by exact_mod_cast (below.2 5 (by decide)).trans (by decide +kernel : _ = (8 : ℚ)),
    by exact_mod_cast (atCutoff.2 5 (by decide)).trans (by decide +kernel : _ = (9 : ℚ))⟩

-- The nonzero residue can exceed the leading digit, giving a negative argument to the ceiling.
example : palindromeAPCount 6 1 3 2 = 0 := by
  have h := palindromeAPCount_of_dvd_base (b := 6) (m := 1) (q := 3)
    (by decide) (by decide) (by decide) (by decide)
  exact_mod_cast (h.2 2 (by decide)).trans (by decide +kernel : _ = (0 : ℚ))

end MetaMathlibExt

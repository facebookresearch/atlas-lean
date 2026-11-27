/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PalindromeCountClosedForm

namespace MetaMathlibExt

-- The minimum base and bound still count the one-digit palindrome, not zero.
example : palindromeAPCount 2 1 1 0 = 1 ∧ palindromeAPCount 2 1 2 0 = 0 ∧
    palindromeAPCount 2 1 2 1 = 1 := by
  decide +kernel

-- The same upper half yields 212 in base four on both sides of the cutoff.
example : palindromicHalfCopy 4 37 = 38 ∧ palindromicHalfCopy 4 38 = 38 := by
  decide +kernel

example : palindromeAPCount 4 37 1 0 = 11 ∧ palindromeAPCount 4 37 2 0 = 3 ∧
    palindromeAPCount 4 37 2 1 = 8 := by
  have h := palindromeCount_closed_form (b := 4) (m := 37) (by decide) (by decide)
  have hp := h.2 (by decide)
  exact ⟨by exact_mod_cast h.1.trans (by decide +kernel : _ = (11 : ℚ)),
    by exact_mod_cast hp.1.trans (by decide +kernel : _ = (3 : ℚ)),
    by exact_mod_cast hp.2.trans (by decide +kernel : _ = (8 : ℚ))⟩

example : palindromeAPCount 4 38 1 0 = 12 ∧ palindromeAPCount 4 38 2 0 = 4 ∧
    palindromeAPCount 4 38 2 1 = 8 := by
  decide +kernel

-- An odd leading digit activates the odd, rather than even, correction.
example : palindromeAPCount 6 5 1 0 = 5 ∧ palindromeAPCount 6 5 2 0 = 2 ∧
    palindromeAPCount 6 5 2 1 = 3 := by
  decide +kernel

-- In an odd base the unconditional formula remains available.
example : palindromeAPCount 3 10 1 0 = 5 := by
  decide +kernel

end MetaMathlibExt

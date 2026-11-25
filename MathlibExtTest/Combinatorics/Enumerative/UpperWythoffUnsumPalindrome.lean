/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsumPalindrome

namespace MetaMathlibExt

-- At the first admissible index, reversing the gap word gives the singleton 3.
example : (upperWythoffUnsumPalindrome 1).reverse = [3] :=
  (upperWythoffUnsumPalindrome_reverse (i := 1) le_rfl).trans upperWythoffUnsumPalindrome_one

-- Reflection identifies individual gaps, including the two outermost positions.
example {i k : ℕ} (hi : 1 ≤ i) (hk : k < (upperWythoffUnsumPalindrome i).length) :
    (upperWythoffUnsumPalindrome i)[k] =
      (upperWythoffUnsumPalindrome i)[(upperWythoffUnsumPalindrome i).length - 1 - k]'(
        Nat.sub_one_sub_lt_of_lt hk) := by
  simpa only [upperWythoffUnsumPalindrome_reverse hi] using List.getElem_eq_getElem_reverse hk

end MetaMathlibExt

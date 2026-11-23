/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsum

namespace MetaMathlibExt

-- Repeated summands are excluded: 2 + 2 leaves 4 an unsum, while 2 + 5 covers 7.
example : IsUpperWythoffUnsum 4 ∧ ¬ IsUpperWythoffUnsum 7 := by
  have h := isUpperWythoffUnsum_small
  constructor
  · simpa using Finset.ext_iff.mp h 4
  · simpa using Finset.ext_iff.mp h 7

-- The first two indices give the same singleton because subtraction is truncated.
example : upperWythoffUnsumPalindrome 0 = [3] ∧ upperWythoffUnsumPalindrome 1 = [3] :=
  ⟨upperWythoffUnsumPalindrome_one, upperWythoffUnsumPalindrome_one⟩

example (k : ℕ) : upperWythoffUnsumPalindrome (k + 1) ≠ [] := by
  have h := (upperWythoffUnsumPalindrome_head_getLast (i := k + 1) (by omega)).1
  rintro he
  simp [he] at h

end MetaMathlibExt

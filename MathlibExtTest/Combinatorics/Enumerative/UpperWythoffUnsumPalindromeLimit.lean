/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsumPalindromeLimit

namespace MetaMathlibExt

-- Check the leading digit and both values of the coding at a common stage.
example : ∃ N, ∀ i ≥ N, (upperWythoffUnsumPalindrome i)[0]? = some 3 ∧
    (upperWythoffUnsumPalindrome i)[1]? = some 5 ∧
    (upperWythoffUnsumPalindrome i)[2]? = some 3 := by
  obtain ⟨a, ha⟩ := upperWythoffUnsumPalindrome_tendsto 0
  obtain ⟨b, hb⟩ := upperWythoffUnsumPalindrome_tendsto 1
  obtain ⟨c, hc⟩ := upperWythoffUnsumPalindrome_tendsto 2
  exact ⟨max a (max b c), fun i hi => ⟨ha i (by omega), hb i (by omega), hc i (by omega)⟩⟩

end MetaMathlibExt

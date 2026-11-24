/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ContinuedFractions.Folding

namespace MetaMathlibExt

-- At the lower bounds for x and aₜ, the normalized block contains both -1 and 0.
example (l : List ℤ) : finiteContFrac (l ++ [0, -1, -3, -2]) =
    finiteContFrac (l ++ [-1, 1, 0, 3, 2]) := by
  simpa using finiteContFrac_neg_block l 0 [2, 3] 1 (by simp +decide) (by decide) (by decide)

-- The suffix [2, 0, -1, -1] has value zero, even after normalization.
example : finiteContFrac [7, 2, 0, -1, -1] = 7 ∧
    finiteContFrac [7, 2, -1, 1, 0, 1] = 7 := by
  norm_num [finiteContFrac]

-- With empty prefix and suffix, opposite neighbours merge to zero.
example (a : ℤ) : finiteContFrac [a, 0, -a] = 0 := by
  simpa [finiteContFrac_singleton] using finiteContFrac_zero_merge [] [] a (-a)

-- The tail [-1, 1] evaluates to zero inside the continued fraction.
example : finiteContFrac [2, 3, 0, -1, 1] = 7 / 3 := calc
  _ = finiteContFrac [2, 2, 1] := finiteContFrac_zero_merge [2] [1] 3 (-1)
  _ = 7 / 3 := by norm_num [finiteContFrac]

end MetaMathlibExt

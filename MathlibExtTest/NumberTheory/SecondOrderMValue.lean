/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SecondOrderMValue
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- A nonintegral value with a positive denominator.
example : secondOrderMValue 2 1 1 1 4 = 31 / 11 := by
  norm_num [secondOrderMValue]

-- At the excluded origin the defining quotient has denominator zero.
example (a b p : ℤ) : secondOrderMValue a b p 0 0 = 0 := by
  simp [secondOrderMValue]

-- The linear identity also applies when the first coordinate vanishes.
example (a b p : ℤ) (hp : p ≠ 0) :
    secondOrderMValue a b p 1 0 + (p ^ 2 + 2) * (b : ℚ) + secondOrderMValue a b p 1 p = 0 := by
  simpa [secondOrderMValue_zero_one] using
    (secondOrderMValue_relations a b p hp 0 1 (by decide)).1

-- For this nonprimitive pair the next second coordinate is zero and the invariant is negative.
example : secondOrderMValue 1 3 (-2) 6 3 ^ 2 +
    6 * secondOrderMValue 1 3 (-2) 6 3 * secondOrderMValue 1 3 (-2) 3 0 +
    secondOrderMValue 1 3 (-2) 3 0 ^ 2 = -56 := by
  have h := (secondOrderMValue_relations 1 3 (-2) (by decide) 6 3 (by decide)).2
  norm_num at h
  exact h

end MetaMathlibExt

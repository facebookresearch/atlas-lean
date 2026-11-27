/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotKlDeficientPerfectWithTwoPowMul
/-! # Tests for deficient-perfect exclusions

Applications of the exclusions for divisors `1` and `p`, including zero exponents.
-/

namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

example : ¬ KLDeficientPerfectWith 2 1 3 1 := by
  simpa using (not_klDeficientPerfectWith_two_pow_mul 2 1 3 0
    (by decide) (by decide) (by decide)).1

example : ¬ KLDeficientPerfectWith 2 1 3 3 := by
  simpa using (not_klDeficientPerfectWith_two_pow_mul 2 1 3 0
    (by decide) (by decide) (by decide)).2

example : ¬ KLDeficientPerfectWith 0 1 6 1 := by
  simpa using (not_klDeficientPerfectWith_two_pow_mul 0 1 3 1
    (by decide) (by decide) (by decide)).1

example : ¬ KLDeficientPerfectWith 0 1 6 3 := by
  simpa using (not_klDeficientPerfectWith_two_pow_mul 0 1 3 1
    (by decide) (by decide) (by decide)).2

example : ¬ KLDeficientPerfectWith 2 3 6 1 := by
  simpa using (not_klDeficientPerfectWith_two_pow_mul 2 3 3 1
    (by decide) (by decide) (by decide)).1

example : ¬ KLDeficientPerfectWith 2 3 6 3 := by
  simpa using (not_klDeficientPerfectWith_two_pow_mul 2 3 3 1
    (by decide) (by decide) (by decide)).2

end MathlibExtTest.NumberTheory.FkPerfect

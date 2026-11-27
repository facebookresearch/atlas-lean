/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DelannoyBinomialCongruence

open MathlibExt.NumberTheory.DelannoyTriangleWanted

-- At p = 2 the second binomial coefficient is out of range.
example : (Nat.choose (2 - 0) (0 + 1) : ZMod 2) +
    (-1) ^ (0 : ℕ) * (Nat.choose (0 + 0) (0 + 1) : ZMod 2) = 0 :=
  choose_add_choose_mod 2 0 0 (by decide) (by decide) (by decide)

-- At p = 5 and j = k = 2, the two coefficients are 1 and 4.
example : (Nat.choose (5 - 2) (2 + 1) : ZMod 5) +
    (-1) ^ (2 : ℕ) * (Nat.choose (2 + 2) (2 + 1) : ZMod 5) = 0 :=
  choose_add_choose_mod 5 2 2 (by decide) (by decide) (by decide)

-- At j = k = p - 2 for p = 5, the first binomial coefficient is out of range.
example : (Nat.choose (5 - 3) (3 + 1) : ZMod 5) +
    (-1) ^ (3 : ℕ) * (Nat.choose (3 + 3) (3 + 1) : ZMod 5) = 0 :=
  choose_add_choose_mod 5 3 3 (by decide) (by decide) (by decide)

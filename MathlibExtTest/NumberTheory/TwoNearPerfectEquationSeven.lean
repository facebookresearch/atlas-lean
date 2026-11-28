/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectEquationSeven

namespace MetaMathlibExt

-- The smallest allowed exponents are b = 2 and k = 3.
example {p : ℕ} (hp : Odd p) :
    15 * ((p : ℤ) ^ 2 + p + 1) ≠ 16 * p ^ 2 + 4 * p + 1 :=
  not_two_near_perfect_eq_seven (b := 2) (k := 3) hp (by decide) (by decide)

-- Beyond the upper bound on b, the odd number p = 5 solves the equation at k = 4, b = 5.
example : ((2 : ℤ) ^ (4 + 1) - 1) * (5 ^ 2 + 5 + 1) =
    2 ^ (4 + 1) * 5 ^ 2 + 2 ^ 5 * 5 + 1 := by decide

end MetaMathlibExt

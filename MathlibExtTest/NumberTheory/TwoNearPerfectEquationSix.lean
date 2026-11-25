/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectEquationSix

namespace MetaMathlibExt

-- At k = 4 and b = 5, the odd solution p = 5 gives two nontrivial divisibilities.
example : (5 : ℤ) ∣ 15 ∧ (6 : ℤ) ∣ 30 :=
  dvd_of_two_near_perfect_eq_six (b := 5) (k := 4) (p := 5) ⟨2, rfl⟩ (by decide)

-- The even solution p = 2 at k = 2 and b = 3 fails the first divisibility.
example : ((2 : ℤ) ^ (2 + 1) - 1) * (2 ^ 2 + 2 + 1) =
    2 ^ (2 + 1) * 2 ^ 2 + 2 ^ 3 * 2 + 1 ∧ ¬ (2 : ℤ) ∣ 2 ^ 2 - 1 := by decide

end MetaMathlibExt

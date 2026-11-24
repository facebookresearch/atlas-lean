/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectOddDivisor
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- Equation (12) holds at `p = 3`, `k = 2`, `b = 1`: both sides are 91.
example : (3 : ℤ) ∣ 2 ^ (2 : ℕ) - 1 :=
  dvd_of_two_near_perfect_eq_twelve (b := 1) (k := 2) (p := 3)
    (hk := by decide) (hb := by decide) (hp := ⟨1, rfl⟩) (h := by norm_num)

-- The theorem uses oddness, not primality: the unit is also allowed by its statement.
example : (1 : ℤ) ∣ 2 ^ (1 : ℕ) - 1 :=
  dvd_of_two_near_perfect_eq_twelve (b := 2) (k := 1) (p := 1)
    (hk := by decide) (hb := by decide) (hp := ⟨0, rfl⟩) (h := by norm_num)

end MetaMathlibExt

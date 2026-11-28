/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NearPerfectPowerTwoDivisibility

namespace MetaMathlibExt

example : (2 : Nat) = 2 :=
  eq_two_of_two_pow_add_one_dvd (a := 3) (b := 2) (hb := by decide) (h := by decide)

-- The next valid exponent is four later.
example : (2 : Nat) = 2 :=
  eq_two_of_two_pow_add_one_dvd (a := 7) (b := 2) (hb := by decide) (h := by decide)

-- At the lower endpoint b = 1, no exponent a works.
example (a : Nat) : ¬ (2 ^ 1 + 1 ∣ 3 * 2 ^ a + 1) := by
  intro h
  exact (by decide : (1 : Nat) ≠ 2)
    (eq_two_of_two_pow_add_one_dvd (a := a) (b := 1) (hb := by decide) (h := h))

-- Omitting hb would admit the counterexample a = b = 0.
example : (2 : Nat) ^ 0 + 1 ∣ 3 * 2 ^ 0 + 1 ∧ (0 : Nat) ≠ 2 := by decide

end MetaMathlibExt

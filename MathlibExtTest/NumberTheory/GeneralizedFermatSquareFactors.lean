/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.GeneralizedFermatSquareFactors

/-! # Tests for squared prime factors of generalized Fermat numbers -/

open MetaMathlibExt

-- At an odd exponent the order can be a proper divisor of twice that exponent.
example : 8 ^ (3 - 1) ≡ 1 [MOD 3 ^ 2] ∧ orderOf (8 : ZMod 3) ∣ 10 ∧
    orderOf (8 : ZMod 3) ≠ 10 := by
  obtain ⟨hw, hd⟩ := (sq_dvd_pow_pow_add_one_wieferich (a := 8) (b := 5) (n := 1) (p := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1 (by decide)
  have ho : orderOf (8 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
  exact ⟨hw, hd, ho ▸ by decide⟩

-- For exponent three, the base 19 has order six modulo seven and lifts modulo 49.
example : 7 ^ 2 ∣ 19 ^ 3 ^ 1 + 1 := by
  apply (sq_dvd_pow_pow_add_one_wieferich (by decide) (by decide) (by decide)
    (by decide) (by decide)).2 (by decide)
  change orderOf (19 : ZMod 7) = 6
  apply (orderOf_eq_iff (by decide)).mpr
  refine ⟨by decide, fun m hm hmpos => ?_⟩
  interval_cases m <;> decide

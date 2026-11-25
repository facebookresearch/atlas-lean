/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexityLowerBound
import Mathlib.Tactic.IntervalCases

/-! # A sharp example of the logarithmic 2-complexity bound -/

namespace MathlibExt.NumberTheory.TwoComplexityWanted

-- The four consecutive bits of 30 end in exponent one, just outside the four-power form.
-- Rounding the logarithmic bound up gives the exact cost of the expression 2 + 2 * 14.
example : complexityL 2 30 = 7 := by
  have two : CanBuild 2 1 2 := CanBuild.base
  have six : CanBuild 2 3 6 := two.add (two.mul two)
  have fourteen : CanBuild 2 5 14 := two.add (two.mul six)
  refine le_antisymm (complexityL_min_le (two.add (two.mul fourteen))) ?_
  have h := logb_two_add_two_le 4 30 (by decide) (by decide) (by decide) (by decide) (by
    rintro ⟨a, b, hab, he⟩
    have hb : b < 5 := by
      by_contra! hb
      have hp : 2 ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
      have hsmall : 2 ^ b ≤ 30 := he ▸ Nat.le_add_left _ _
      omega
    interval_cases b <;> interval_cases a <;> norm_num at he) (by
    rintro (⟨a, b, ha, hb, hb₁, he⟩ | ⟨a, b, c, ha, hb, hc, hc₂, -, -⟩ | ⟨a, ha, ha₆, -⟩ | h)
    · interval_cases a <;> interval_cases b <;> norm_num at he
    all_goals omega)
  have hlog : (4 : ℝ) < Real.logb 2 30 := calc
    (4 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 4) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    _ < _ := Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  exact_mod_cast (show (6 : ℝ) < (complexityL 2 30 : ℝ) by linarith)

end MathlibExt.NumberTheory.TwoComplexityWanted

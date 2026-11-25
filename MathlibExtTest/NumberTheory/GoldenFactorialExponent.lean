/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GoldenFactorialExponent

namespace MetaMathlibExt

open Real

-- The lower bound is attained at the first index allowed by the hypothesis.
example : goldenFactorialExponent 2 =
    goldenFactorialExponent (2 - 1) + ⌊Real.logb goldenRatio (2 : ℕ)⌋₊ := by
  refine le_antisymm ?_ (goldenFactorialExponent_succ_bounds (n := 2) (hn := by decide)).1
  have hfloor : 1 ≤ ⌊Real.logb goldenRatio (2 : ℕ)⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one, Real.le_logb_iff_rpow_le one_lt_goldenRatio (by norm_num), Real.rpow_one]
    exact_mod_cast goldenRatio_lt_two.le
  rw [show 2 - 1 = 1 by decide, goldenFactorialExponent_one, goldenFactorialExponent_two]
  omega

-- The upper bound is attained at four.
example : goldenFactorialExponent 4 =
    goldenFactorialExponent (4 - 1) + ⌊Real.logb goldenRatio (4 : ℕ)⌋₊ + 1 := by
  refine le_antisymm (goldenFactorialExponent_succ_bounds (n := 4) (hn := by decide)).2 ?_
  have hlo : (3 / 2 : ℝ) < goldenRatio := by
    have hsqrt : (2 : ℝ) < Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
    unfold goldenRatio
    linarith
  have hcube : goldenRatio ^ (3 : ℕ) = 2 * goldenRatio + 1 := by
    rw [pow_succ, goldenRatio_sq]
    nlinarith [goldenRatio_sq]
  have hquartic : goldenRatio ^ (4 : ℕ) = 3 * goldenRatio + 2 := by
    rw [pow_succ, hcube]
    nlinarith [goldenRatio_sq]
  have hsixth : goldenRatio ^ (6 : ℕ) = 8 * goldenRatio + 5 := by
    change goldenRatio ^ (3 * 2 : ℕ) = _
    rw [pow_mul, hcube]
    nlinarith [goldenRatio_sq]
  have hprev : goldenFactorialExponent 3 ≤ 4 := by
    apply goldenFactorialExponent_le (by decide)
    norm_num [Nat.factorial, hquartic]
    linarith
  have hfloor : ⌊Real.logb goldenRatio (4 : ℕ)⌋₊ < 3 := by
    apply (Nat.floor_lt' (by decide)).mpr
    rw [Real.logb_lt_iff_lt_rpow one_lt_goldenRatio (by norm_num)]
    norm_num [Real.rpow_ofNat, hcube]
    linarith
  have hlarge : 6 < goldenFactorialExponent 4 := by
    by_contra! hle
    have hbound := (goldenFactorialExponent_mem 4).2.trans
      (pow_le_pow_right₀ one_lt_goldenRatio.le hle)
    norm_num [Nat.factorial, hsixth] at hbound
    linarith [goldenRatio_lt_two]
  change goldenFactorialExponent 3 + ⌊Real.logb goldenRatio (4 : ℕ)⌋₊ + 1 ≤ _
  omega

end MetaMathlibExt

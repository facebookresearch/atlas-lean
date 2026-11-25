/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.MersenneTenPowBlockLength
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for the block-length power of ten modulo a Mersenne prime -/

open MetaMathlibExt

-- `p = 3`: `1/7 = 0.(142857)` has period `L = 6`, so the hypotheses hold and the blocks have
-- `L / p = 2` digits. The exponent the theorem gives is forced to be `1`:
-- `10 ^ 2 = 100 ≡ 2 (mod 7)`, while `2 ^ 2 = 4`.
example : ∃ r ∈ Finset.Icc 1 2, 10 ^ 2 ≡ 2 ^ r [MOD 7] ∧ r = 1 := by
  have hord : orderOf (10 : ZMod (2 ^ 3 - 1)) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  obtain ⟨r, hr, hmod⟩ :=
    ten_pow_blockLength_modEq_two_pow 3 (by norm_num) (by rw [hord]; norm_num)
  rw [hord] at hmod
  refine ⟨r, hr, hmod, ?_⟩
  rw [Finset.mem_Icc] at hr
  obtain ⟨h1, h2⟩ := hr
  interval_cases r
  · rfl
  · exact absurd hmod (by decide)

-- `p = 5`: `1/31` has period `L = 15`, and the blocks have `3` digits. The exponent is `3`,
-- since `10 ^ 3 = 1000 ≡ 8 = 2 ^ 3 (mod 31)`: it need not be `1`.
example : ∃ r ∈ Finset.Icc 1 4, 10 ^ 3 ≡ 2 ^ r [MOD 31] ∧ r = 3 := by
  have hord : orderOf (10 : ZMod (2 ^ 5 - 1)) = 15 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  obtain ⟨r, hr, hmod⟩ :=
    ten_pow_blockLength_modEq_two_pow 5 (by norm_num) (by rw [hord]; norm_num)
  rw [hord] at hmod
  refine ⟨r, hr, hmod, ?_⟩
  rw [Finset.mem_Icc] at hr
  obtain ⟨h1, h2⟩ := hr
  interval_cases r <;> first | rfl | exact absurd hmod (by decide)

-- `p = 2`: `10 ≡ 1 (mod 3)` has order `1`, which `p` does not divide, and the conclusion fails:
-- the divisibility hypothesis cannot be dropped.
example : ¬ 2 ∣ orderOf (10 : ZMod (2 ^ 2 - 1)) ∧
    ¬ ∃ r ∈ Finset.Icc 1 (2 - 1),
      10 ^ (orderOf (10 : ZMod (2 ^ 2 - 1)) / 2) ≡ 2 ^ r [MOD 2 ^ 2 - 1] := by
  have hord : orderOf (10 : ZMod (2 ^ 2 - 1)) = 1 := orderOf_eq_one_iff.mpr (by decide)
  rw [hord]
  decide

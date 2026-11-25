/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.FloorSubTwoIdentity

namespace MetaMathlibExt.beatty_floor_inv_sub_eq_floor_sub_two

open Real

/-- The conjugate exponent of `√2` is `2 + √2`. -/
private theorem sqrt_two_inv_add_inv : (√2)⁻¹ + (2 + √2)⁻¹ = 1 := by
  rw [inv_add_inv (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)]
  linarith [mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

-- For α = √2 the conjugate exponent is β = 2 + √2, so β - 2 = α: the right-hand side is the
-- Beatty sequence of α itself.
private theorem sqrt_two {n : ℤ} (hn : 0 < n) :
    ⌊(√2)⁻¹ * (beattySeq (2 + √2) n : ℝ)⌋ - ⌊(√2)⁻¹ * ((beattySeq (√2) n + 1 : ℤ) : ℝ)⌋ =
      beattySeq (√2) n := by
  have h := beatty_floor_inv_sub_eq_floor_sub_two irrational_sqrt_two one_lt_sqrt_two
    (by linarith [sqrt_two_lt_three_halves]) sqrt_two_inv_add_inv hn
  rwa [add_sub_cancel_left] at h

-- At n = 3 the terms are a₃ = ⌊3√2⌋ = 4 and b₃ = ⌊3(2 + √2)⌋ = 10.
example : ⌊(√2)⁻¹ * 10⌋ - ⌊(√2)⁻¹ * 5⌋ = 4 := by
  have hlo : 4 / 3 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi := sqrt_two_lt_three_halves
  have ha : beattySeq (√2) 3 = 4 := by
    rw [beattySeq, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hb : beattySeq (2 + √2) 3 = 10 := by
    rw [beattySeq, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have h := sqrt_two (n := 3) (by decide)
  rw [ha, hb] at h
  norm_num at h
  exact h

end MetaMathlibExt.beatty_floor_inv_sub_eq_floor_sub_two

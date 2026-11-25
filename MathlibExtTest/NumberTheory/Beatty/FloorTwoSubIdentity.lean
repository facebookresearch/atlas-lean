/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.FloorTwoSubIdentity

namespace MetaMathlibExt

open Real

private theorem sqrt_two_floor_diff {n : ℤ} (hn : 0 < n) :
    ⌊(2 + √2)⁻¹ * ((beattySeq (2 + √2) (n - 1) + 1 : ℤ) : ℝ)⌋ -
      ⌊(2 + √2)⁻¹ * (beattySeq (√2) n : ℝ)⌋ = beattySeq (2 - √2) n := by
  have hconj : (√2)⁻¹ + (2 + √2)⁻¹ = 1 := by
    rw [inv_add_inv (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)]
    linarith [mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact beatty_floor_inv_sub_eq_floor_two_sub irrational_sqrt_two one_lt_sqrt_two
    (by linarith [sqrt_two_lt_three_halves]) hconj hn

-- The least positive index uses b₀, not b₁, in the first floor.
example :
    ⌊(2 + √2)⁻¹ * ((beattySeq (2 + √2) (1 - 1) + 1 : ℤ) : ℝ)⌋ -
      ⌊(2 + √2)⁻¹ * (beattySeq (√2) 1 : ℝ)⌋ = 0 := by
  rw [sqrt_two_floor_diff (n := 1) (by decide), beattySeq, Int.floor_eq_iff]
  norm_num
  linarith [one_lt_sqrt_two]

-- With the same complementary pair, the difference is already nonzero at n = 3.
example :
    ⌊(2 + √2)⁻¹ * ((beattySeq (2 + √2) (3 - 1) + 1 : ℤ) : ℝ)⌋ -
      ⌊(2 + √2)⁻¹ * (beattySeq (√2) 3 : ℝ)⌋ = 1 := by
  have hlo : 4 / 3 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  rw [sqrt_two_floor_diff (n := 3) (by decide), beattySeq, Int.floor_eq_iff]
  norm_num
  constructor <;> linarith [hlo, sqrt_two_lt_three_halves]

end MetaMathlibExt

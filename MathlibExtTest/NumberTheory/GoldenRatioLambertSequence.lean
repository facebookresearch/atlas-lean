/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.NumberTheory.GoldenRatioLambertSequence

namespace MetaMathlibExt

open Real

-- The bound holds at the first allowed index, where the lower-branch value exists.
example : ∃ a : ℝ, 3 ≤ a ∧
    lambertMap (-a / 3) = -(1 / 3) * (4 / 7 : ℝ) ^ (1 / 3 : ℝ) ∧
    4 < 3 / 4 * a := by
  let r : ℝ := (4 / 7 : ℝ) ^ (1 / 3 : ℝ)
  have hr₀ : 0 < r := rpow_pos_of_pos (by norm_num) _
  have hr₁ : r ≤ 1 := rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  have he : (1 / 3 : ℝ) < exp (-1) := by
    rw [exp_neg, one_div]
    exact (inv_lt_inv₀ (by norm_num) (exp_pos _)).mpr exp_one_lt_three
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    (existsUnique_lambertMap_lower_preimage (x := -(1 / 3) * r)
      (by linarith) (by linarith)).exists
  have ha : 3 ≤ -3 * y := by linarith [show y ≤ -1 from hy]
  have hW : lambertMap (-(-3 * y) / 3) = -(1 / 3) * r := by
    rw [show -(-3 * y) / 3 = y by ring]
    exact hxy
  refine ⟨-3 * y, ha, hW, ?_⟩
  have hd : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
  have h := two_mul_sub_four_lt_lambertSequence 4 (by norm_num) (-3 * y)
    (by rw [hd]; exact ha) (by rw [hd]; exact hW)
  rwa [show 2 * ((4 : ℕ) : ℝ) - 4 = 4 by norm_num] at h

end MetaMathlibExt

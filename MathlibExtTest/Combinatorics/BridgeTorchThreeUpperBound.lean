/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BridgeTorchThreeUpperBound
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.BridgeTorchGeneralizations

-- At the smallest admissible population the bound is the integer 17.
example : bridgeTime 3 7 ≤ 17 := by
  have h := bridgeTime_three_le_closed_form 7 le_rfl
  rw [show 2 * ((7 : ℕ) : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 + (2 : ℕ) * (2 * Real.pi) by
    push_cast; ring, Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub, Real.cos_pi_div_three] at h
  norm_num at h
  exact_mod_cast h

-- For a multiple of six, `(-1) ^ n = 1` and `cos (2nπ / 3) = 1`, and the bound is 43.
example : bridgeTime 3 12 ≤ 43 := by
  have h := bridgeTime_three_le_closed_form 12 (by norm_num)
  rw [show 2 * ((12 : ℕ) : ℝ) * Real.pi / 3 = (4 : ℕ) * (2 * Real.pi) by push_cast; ring,
    Real.cos_nat_mul_two_pi] at h
  norm_num at h
  exact_mod_cast h

-- Beyond twelve people the bound grows by `2n + 6` every six people: at 13 it is 17 + 32.
example : bridgeTime 3 13 ≤ 49 := by
  have h := bridgeTime_three_le_closed_form 13 (by norm_num)
  rw [show 2 * ((13 : ℕ) : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 + (4 : ℕ) * (2 * Real.pi) by
    push_cast; ring, Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub, Real.cos_pi_div_three] at h
  norm_num at h
  exact_mod_cast h

end MetaMathlibExt.BridgeTorchGeneralizations

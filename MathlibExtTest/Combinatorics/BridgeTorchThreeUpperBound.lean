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

-- At the six-step threshold, a single crossing for the remaining three costs 3.
example : bridgeTime 3 9 ≤ 27 := by
  have h : IsBridgeSchedule 3 3 [{1, 2, 3}] := by unfold IsBridgeSchedule; decide
  have hsmall : bridgeTime 3 3 ≤ 3 := bridgeTime_le_scheduleCost h
  have hstep : bridgeTime 3 9 ≤ bridgeTime 3 3 + 24 := bridgeTime_three_le_sub_six 9 (by decide)
  exact hstep.trans (Nat.add_le_add_right hsmall 24)

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

-- Integrality and both gap bounds determine the value without evaluating the cosine.
private theorem closedForm_eq_ceil (n : ℕ) (hn : 7 ≤ n) :
    (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
        2 / 9 * Real.cos (2 * n * Real.pi / 3) = ⌈(n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2⌉ := by
  obtain ⟨⟨z, hz⟩, hlo, hhi⟩ := closedForm_U_integral_and_near_V n hn
  rw [hz] at hlo hhi ⊢
  exact_mod_cast (Int.ceil_eq_iff.mpr ⟨by linarith, by linarith⟩ :
    ⌈(n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2⌉ = z).symm

-- At the first admissible population the lower bound rounds up from 50/3 to 17.
example : (7 : ℝ) ^ 2 / 6 + 2 * 7 - 181 / 36 + (-1 : ℝ) ^ 7 / 4 -
    2 / 9 * Real.cos (2 * 7 * Real.pi / 3) = 17 := by
  convert closedForm_eq_ceil 7 le_rfl using 1
  norm_num

-- At nine people the lower bound is already an integer and the gap is zero.
example : (9 : ℝ) ^ 2 / 6 + 2 * 9 - 181 / 36 + (-1 : ℝ) ^ 9 / 4 -
    2 / 9 * Real.cos (2 * 9 * Real.pi / 3) = 26 := by
  convert closedForm_eq_ceil 9 (by decide) using 1
  norm_num

end MetaMathlibExt.BridgeTorchGeneralizations

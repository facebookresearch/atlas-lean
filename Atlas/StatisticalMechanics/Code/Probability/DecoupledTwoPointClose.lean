/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Code.Probability.SharpThresholdWire

open scoped BigOperators
open Real Set

namespace StatMech.Probability

set_option linter.style.longLine false





theorem dtpc_witness_lhs :
    ((1 - (9 / 10 : ℝ)) * 1 + (9 / 10) * 0) ^ 2
        + (1 / 2 : ℝ) ^ 2 * ((9 / 10) * (1 - 9 / 10)) * (1 - 0) ^ 2 = 13 / 400 := by
  norm_num




theorem dtpc_witness_rhs :
    ((1 - (9 / 10 : ℝ)) * |(1 : ℝ)| ^ (1 + (1 / 2 : ℝ) ^ 2)
          + (9 / 10) * |(0 : ℝ)| ^ (1 + (1 / 2 : ℝ) ^ 2)) ^ (2 / (1 + (1 / 2 : ℝ) ^ 2))
      = ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5) := by
  have hq : (1 : ℝ) + (1 / 2 : ℝ) ^ 2 = 5 / 4 := by norm_num
  rw [hq]
  rw [show |(1 : ℝ)| = 1 by norm_num, show |(0 : ℝ)| = 0 by norm_num]
  rw [Real.one_rpow, Real.zero_rpow (by norm_num : (5 : ℝ) / 4 ≠ 0)]
  rw [show (2 : ℝ) / (5 / 4) = 8 / 5 by norm_num]
  norm_num







theorem dtpc_witness_rhs_lt_lhs : ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5) < 13 / 400 := by
  have hy : (0 : ℝ) ≤ 13 / 400 := by norm_num
  
  have hcube_x : (((1 : ℝ) / 10) ^ ((8 : ℝ) / 5)) ^ (5 : ℕ) = ((1 : ℝ) / 10) ^ (8 : ℝ) := by
    rw [← Real.rpow_natCast (((1 : ℝ) / 10) ^ ((8 : ℝ) / 5)) 5, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h10_8 : ((1 : ℝ) / 10) ^ (8 : ℝ) = 1 / 100000000 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hlt : (((1 : ℝ) / 10) ^ ((8 : ℝ) / 5)) ^ (5 : ℕ) < ((13 : ℝ) / 400) ^ (5 : ℕ) := by
    rw [hcube_x, h10_8]; norm_num
  by_contra hc
  rw [not_lt] at hc
  exact absurd (pow_le_pow_left₀ hy hc 5) (not_le.mpr hlt)











theorem dtpc_pbiasedHCLib_nine_tenths_false : ¬ PBiasedHCLib (9 / 10) := by
  intro H
  
  have h := H (1 / 2) (by norm_num) (by norm_num) 1 0
  rw [dtpc_witness_rhs] at h
  
  rw [dtpc_witness_lhs] at h
  exact absurd h (not_le.mpr dtpc_witness_rhs_lt_lhs)












theorem dtpc_remainingGoal_false {q : ℝ} (hq : (9 : ℝ) / 10 < q) :
    ¬ stw_RemainingGoal q := by
  intro H
  have hmem : (9 / 10 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) q := ⟨by norm_num, hq⟩
  exact dtpc_pbiasedHCLib_nine_tenths_false (H (9 / 10) hmem)














theorem dtpc_coupled_true_at_witness :
    ((1 - (9 / 10 : ℝ)) * 1 + (9 / 10) * 0) ^ 2
        + (1 / 2 : ℝ) ^ 2 * (2 * (9 / 10) * (1 - 9 / 10)) ^ 2 * (1 - 0) ^ 2
      ≤ ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5) := by
  have hcoupled_lhs : ((1 - (9 / 10 : ℝ)) * 1 + (9 / 10) * 0) ^ 2
        + (1 / 2 : ℝ) ^ 2 * (2 * (9 / 10) * (1 - 9 / 10)) ^ 2 * (1 - 0) ^ 2 = 181 / 10000 := by
    norm_num
  rw [hcoupled_lhs]
  
  have hx : (0 : ℝ) ≤ ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5) := Real.rpow_nonneg (by norm_num) _
  have hcube_x : (((1 : ℝ) / 10) ^ ((8 : ℝ) / 5)) ^ (5 : ℕ) = ((1 : ℝ) / 10) ^ (8 : ℝ) := by
    rw [← Real.rpow_natCast (((1 : ℝ) / 10) ^ ((8 : ℝ) / 5)) 5, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h10_8 : ((1 : ℝ) / 10) ^ (8 : ℝ) = 1 / 100000000 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hle5 : ((181 : ℝ) / 10000) ^ (5 : ℕ) ≤ (((1 : ℝ) / 10) ^ ((8 : ℝ) / 5)) ^ (5 : ℕ) := by
    rw [hcube_x, h10_8]; norm_num
  by_contra hc
  rw [not_le] at hc
  have : (((1 : ℝ) / 10) ^ ((8 : ℝ) / 5)) ^ (5 : ℕ) < ((181 : ℝ) / 10000) ^ (5 : ℕ) :=
    pow_lt_pow_left₀ hc hx (by norm_num)
  linarith

end StatMech.Probability

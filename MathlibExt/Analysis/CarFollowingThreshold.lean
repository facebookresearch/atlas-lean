/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Analysis.CarFollowingGain
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Car-following gain threshold

For sensitivity `lambda > 0` and delay `T ≥ 0` in the delayed
car-following model, the gain stays strictly below one at every
positive frequency, in the form `omega > 2 * lambda * sin (omega * T)`
for all `omega > 0`, if and only if `lambda * T ≤ 1 / 2`. The
boundary `lambda * T = 1 / 2` is included: there `sin x < x` keeps
the inequality strict, while any `lambda * T > 1 / 2` fails at a
sufficiently small frequency.

## Main results

- `CarFollowingGain.gain_threshold_all_frequencies`: the
  characterization.
-/

@[expose] public section

/-- All-frequency gain threshold for the car-following model. For
`lambda > 0` and `T ≥ 0`, the inequality
`omega > 2 * lambda * sin (omega * T)` holds at every positive
frequency `omega` if and only if `lambda * T ≤ 1 / 2`. By the
frequency-response analysis of the model this is the condition
that the transfer denominator never vanishes and the gain stays
strictly below one at every positive frequency; the boundary
`lambda * T = 1 / 2` is included. -/
theorem CarFollowingGain.gain_threshold_all_frequencies {lambda T : ℝ}
    (hlambda : 0 < lambda) (hT : 0 ≤ T) :
    (∀ omega : ℝ, 0 < omega → omega > 2 * lambda * Real.sin (omega * T))
      ↔ lambda * T ≤ 1 / 2 := by
  constructor
  · intro hall
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hT with rfl | hTpos
    · rw [mul_zero] at hcon
      norm_num at hcon
    · have h2lpos : (0 : ℝ) < 2 * lambda := by linarith
      have h2lTpos : (0 : ℝ) < 2 * lambda * T := mul_pos h2lpos hTpos
      have h2lT : (1 : ℝ) < 2 * lambda * T := by linarith
      have h2lTne : (2 : ℝ) * lambda * T ≠ 0 := ne_of_gt h2lTpos
      have hTne : T ≠ 0 := ne_of_gt hTpos
      set c : ℝ := 1 - 1 / (2 * lambda * T) with hc
      have hinv0 : (0 : ℝ) < 1 / (2 * lambda * T) := one_div_pos.mpr h2lTpos
      have hinv1 : (1 : ℝ) / (2 * lambda * T) < 1 := (div_lt_one h2lTpos).mpr h2lT
      have hc0 : (0 : ℝ) < c := by rw [hc]; linarith
      have hc1 : c < 1 := by rw [hc]; linarith
      have hrel : (2 * lambda * T) * (1 - c) = 1 := by
        have h2 : (1 : ℝ) - c = 1 / (2 * lambda * T) := by rw [hc]; ring
        rw [h2, mul_one_div_cancel h2lTne]
      set w : ℝ := c / T with hw
      have hwpos : (0 : ℝ) < w := by rw [hw]; exact div_pos hc0 hTpos
      have hwT : w * T = c := by rw [hw]; exact div_mul_cancel₀ c hTne
      have hTc : T * w = c := by rw [mul_comm]; exact hwT
      have hmain := hall w hwpos
      rw [hwT] at hmain
      have hsin := Real.sin_gt_sub_cube hc0
      have hkey : w ≤ 2 * lambda * (c - c ^ 3 / 6) := by
        apply le_of_mul_le_mul_left _ hTpos
        rw [hTc]
        have hrewrite : T * (2 * lambda * (c - c ^ 3 / 6))
            = (2 * lambda * T) * (c - c ^ 3 / 6) := by ring
        rw [hrewrite]
        have hexpand : (2 * lambda * T) * (c - c ^ 3 / 6) - c
            = (2 * lambda * T) * c ^ 2 * (1 - c / 6)
              + c * ((2 * lambda * T) * (1 - c) - 1) := by ring
        have hnonneg : (0 : ℝ) ≤ (2 * lambda * T) * c ^ 2 * (1 - c / 6) :=
          mul_nonneg (mul_nonneg (le_of_lt h2lTpos) (sq_nonneg c)) (by linarith)
        have hzero : c * ((2 * lambda * T) * (1 - c) - 1) = 0 := by
          rw [hrel, sub_self, mul_zero]
        have hdiff : (0 : ℝ) ≤ (2 * lambda * T) * (c - c ^ 3 / 6) - c := by
          rw [hexpand, hzero, add_zero]
          exact hnonneg
        linarith
      have hlt : 2 * lambda * (c - c ^ 3 / 6) < 2 * lambda * Real.sin c :=
        mul_lt_mul_of_pos_left hsin h2lpos
      linarith
  · intro hle omega homega
    rcases eq_or_lt_of_le hT with rfl | hTpos
    · rw [mul_zero, Real.sin_zero, mul_zero]
      exact homega
    · have hx : (0 : ℝ) < omega * T := mul_pos homega hTpos
      have hsin := Real.sin_lt hx
      have h2lpos : (0 : ℝ) < 2 * lambda := by linarith
      have hmul : 2 * lambda * Real.sin (omega * T) < 2 * lambda * (omega * T) :=
        mul_lt_mul_of_pos_left hsin h2lpos
      have hle2 : 2 * lambda * T ≤ 1 := by linarith
      have hle3 : 2 * lambda * (omega * T) ≤ omega := by
        have hrw : 2 * lambda * (omega * T) = omega * (2 * lambda * T) := by ring
        rw [hrw]
        calc omega * (2 * lambda * T) ≤ omega * 1 :=
              mul_le_mul_of_nonneg_left hle2 (le_of_lt homega)
            _ = omega := mul_one omega
      exact lt_of_lt_of_le hmul hle3


/-- All-frequency gain threshold for the car-following transfer
function: the gain `‖λ * exp (-(I * w * T))‖ < ‖denom λ T w‖`
holds at every positive frequency `w` if and only if
`lambda * T ≤ 1 / 2`. This composes `CarFollowingGain.gain_lt_one_iff`
with `CarFollowingGain.gain_threshold_all_frequencies`. -/
theorem CarFollowingGain.gain_lt_one_all_frequencies {lam T : ℝ}
    (hlam : 0 < lam) (hT : 0 ≤ T) :
    (∀ w : ℝ, 0 < w → ‖(lam : ℂ) * Complex.exp (-(Complex.I * w * T))‖
        < ‖CarFollowingGain.denom lam T w‖)
      ↔ lam * T ≤ 1 / 2 := by
  constructor
  · intro h
    rw [← CarFollowingGain.gain_threshold_all_frequencies hlam hT]
    intro w hw
    exact (CarFollowingGain.gain_lt_one_iff hlam hw).1 (h w hw)
  · intro h w hw
    exact (CarFollowingGain.gain_lt_one_iff hlam hw).2
      ((CarFollowingGain.gain_threshold_all_frequencies hlam hT).2 h w hw)

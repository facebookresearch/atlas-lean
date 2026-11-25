/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Instrumentation.DACLevelError
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Instrumentation.DACLevelError
open MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp

namespace PhyslibExtTest.Instrumentation.DACLevelError

/-- Fixture level error: `1 / 4` at even codes and `-1 / 4` at odd
codes. -/
private noncomputable def alternatingError (k : ℤ) : ℝ :=
  if Even k then 1 / 4 else -(1 / 4)

/-- The alternating fixture error has magnitude `1 / 4` at every
code, so it satisfies the level-error bound with `η = 1 / 4` on the
signed two-bit range. -/
private lemma alternatingError_abs (k : ℤ) : |alternatingError k| = 1 / 4 := by
  unfold alternatingError
  split <;> norm_num

/-- **Signed 2-bit fixture.** `Δ = 1`, codes `-2 .. 1`, `η = 1 / 4`,
error `alternatingError`: the levels are `-7/4, -5/4, 1/4, 3/4`
(negative and positive codes); the step from code `-1` to `0` has
error exactly `2 * η`; the ADC maps both endpoints `-2` and `1` to
themselves; and the negative input `-3/5` maps to code `-1`. -/
private lemma signedTwoBit_fixture :
    dacLevel 1 alternatingError (-2) = -7 / 4 ∧ dacLevel 1 alternatingError (-1) = -5 / 4 ∧
      dacLevel 1 alternatingError 0 = 1 / 4 ∧ dacLevel 1 alternatingError 1 = 3 / 4 ∧
      |dacLevel 1 alternatingError 0 - dacLevel 1 alternatingError (-1) - 1| = 2 * (1 / 4) ∧
      code 1 (-2) 1 (-2) = -2 ∧ code 1 (-2) 1 1 = 1 ∧ code 1 (-2) 1 (-3 / 5) = -1 := by
  have hE_neg2 : Even (-2 : ℤ) := ⟨-1, by norm_num⟩
  have hO_neg1 : ¬ Even (-1 : ℤ) := by
    rintro ⟨r, h⟩
    omega
  have hE_0 : Even (0 : ℤ) := ⟨0, by norm_num⟩
  have hO_1 : ¬ Even (1 : ℤ) := by
    rintro ⟨r, h⟩
    omega
  have e_neg2 : alternatingError (-2) = 1 / 4 := by
    unfold alternatingError
    exact if_pos hE_neg2
  have e_neg1 : alternatingError (-1) = -(1 / 4) := by
    unfold alternatingError
    exact if_neg hO_neg1
  have e_0 : alternatingError 0 = 1 / 4 := by
    unfold alternatingError
    exact if_pos hE_0
  have e_1 : alternatingError 1 = -(1 / 4) := by
    unfold alternatingError
    exact if_neg hO_1
  have L_neg2 : dacLevel 1 alternatingError (-2) = -7 / 4 := by
    simp only [dacLevel, e_neg2]
    push_cast
    norm_num
  have L_neg1 : dacLevel 1 alternatingError (-1) = -5 / 4 := by
    simp only [dacLevel, e_neg1]
    push_cast
    norm_num
  have L_0 : dacLevel 1 alternatingError 0 = 1 / 4 := by
    simp only [dacLevel, e_0]
    push_cast
    norm_num
  have L_1 : dacLevel 1 alternatingError 1 = 3 / 4 := by
    simp only [dacLevel, e_1]
    push_cast
    norm_num
  have hstep : |dacLevel 1 alternatingError 0 - dacLevel 1 alternatingError (-1) - 1|
      = 2 * (1 / 4) := by
    rw [L_0, L_neg1]
    norm_num
  have r_neg2 : round ((-2 : ℝ) / 1) = -2 := by
    norm_num [round_eq]
  have r_1 : round ((1 : ℝ) / 1) = 1 := by
    norm_num [round_eq]
  have r_neg35 : round ((-3 / 5 : ℝ) / 1) = -1 := by
    norm_num [round_eq]
  have c_neg2 : code 1 (-2) 1 (-2) = -2 := by
    unfold MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp.code
    rw [r_neg2]
    decide
  have c_1 : code 1 (-2) 1 1 = 1 := by
    unfold MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp.code
    rw [r_1]
    decide
  have c_neg35 : code 1 (-2) 1 (-3 / 5) = -1 := by
    unfold MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp.code
    rw [r_neg35]
    decide
  exact ⟨L_neg2, L_neg1, L_0, L_1, hstep, c_neg2, c_1, c_neg35⟩

/-- Adjacent steps at concrete codes: the step from code `-1` to
code `0` attains the `2 * η` step-error bound. -/
example : |dacLevel 1 alternatingError 0 - dacLevel 1 alternatingError (-1) - 1|
    ≤ 2 * (1 / 4 : ℝ) := by
  have he : ∀ k ∈ Set.Icc (-2 : ℤ) 1, |alternatingError k| ≤ (1 / 4 : ℝ) :=
    fun k _ => le_of_eq (alternatingError_abs k)
  have h : |dacLevel 1 alternatingError ((-1 : ℤ) + 1)
      - dacLevel 1 alternatingError (-1) - 1| ≤ 2 * (1 / 4 : ℝ) :=
    abs_dacLevel_add_one_sub_sub_le he (show (-2 : ℤ) ≤ -1 by norm_num)
      (show (-1 : ℤ) + 1 ≤ 1 by norm_num)
  simpa using h

/-- Level monotonicity at concrete steps: with `Δ = 1` and
`η = 1 / 4`, so `2 * η < Δ`, the fixture levels increase from the
least signed two-bit code to the greatest. -/
example : dacLevel 1 alternatingError (-2) < dacLevel 1 alternatingError 1 :=
  dacLevel_strictMonoOn (kmin := -2) (kmax := 1)
    (fun k _ => le_of_eq (alternatingError_abs k)) (by norm_num)
    (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) (by norm_num)

/-- The code error bound on a concrete unclipped input: the
full-scale input `-3 / 5` is unclipped for the signed two-bit
range, and the DAC output at its saturating code is within
`1 / 2 + 1 / 4` of it. -/
example : |dacLevel 1 alternatingError (code 1 (-2) 1 (-3 / 5 : ℝ)) - (-3 / 5 : ℝ)|
    ≤ 1 / 2 + 1 / 4 :=
  abs_dacLevel_code_sub_le_of_not_isClipped (by norm_num)
    (fun k _ => le_of_eq (alternatingError_abs k))
    (not_isClipped_of_mem_Icc (by norm_num)
      (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩))

end PhyslibExtTest.Instrumentation.DACLevelError

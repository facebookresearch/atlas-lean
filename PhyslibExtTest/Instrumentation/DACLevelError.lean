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

/-- The alternating fixture error has magnitude `1 / 4` at every
code, so it satisfies the level-error bound with `η = 1 / 4` on the
signed two-bit range. -/
private lemma alternatingError_abs (k : ℤ) : |alternatingError k| = 1 / 4 := by
  unfold alternatingError
  split <;> norm_num

/-- The signed two-bit fixture, as proved for the public levels. -/
example : dacLevel 1 alternatingError (-2) = -7 / 4
    ∧ dacLevel 1 alternatingError (-1) = -5 / 4
    ∧ dacLevel 1 alternatingError 0 = 1 / 4
    ∧ dacLevel 1 alternatingError 1 = 3 / 4 :=
  ⟨signedTwoBit_fixture.1, signedTwoBit_fixture.2.1,
    signedTwoBit_fixture.2.2.1, signedTwoBit_fixture.2.2.2.1⟩

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

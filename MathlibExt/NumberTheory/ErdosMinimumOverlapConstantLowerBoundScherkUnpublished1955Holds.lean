/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant
import MathlibExt.NumberTheory.ErdosMinimumOverlapMoser

/-! # Scherk's lower bound for minimum overlap -/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-- **Scherk's lower bound for the minimum-overlap constant (statement).** The statement that the
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $1 - 1/\sqrt{2} \le C_{1b}$.

Source: Scherk, unpublished 1955; Optimization Problems, Constant 1b. -/
def lowerBound_Scherk_unpublished_1955 : Prop := 1 - 1 / Real.sqrt 2 ≤ C₁ᵦ

/-- **Scherk's lower bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $1 - 1/\sqrt{2} \le C_{1b}$.

Source: Scherk, unpublished 1955, recorded by Optimization Problems 1b. -/
public theorem lowerBound_Scherk_unpublished_1955_holds :
  lowerBound_Scherk_unpublished_1955 := by
  have h₂ : 0 < Real.sqrt 2 := by positivity
  have h₂_le : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hdiv : (2 : ℝ) / 3 ≤ 1 / Real.sqrt 2 := by
    apply (le_div_iff₀ h₂).2
    linarith
  have h₁₅ : Real.sqrt 15 ≤ (35 : ℝ) / 9 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  calc
    1 - 1 / Real.sqrt 2 ≤ (1 : ℝ) / 3 := by linarith
    _ ≤ Real.sqrt (4 - Real.sqrt 15) := by
      apply (Real.le_sqrt (by norm_num) (by linarith)).2
      norm_num
      linarith
    _ ≤ C₁ᵦ := lowerBound_M1959_holds

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

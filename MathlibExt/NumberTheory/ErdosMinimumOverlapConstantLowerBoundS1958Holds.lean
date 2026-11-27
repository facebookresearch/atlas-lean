/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant
import MathlibExt.NumberTheory.ErdosMinimumOverlapMoser

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-- **The proposition $(4 - \sqrt{6})/5 \le C_{1b}$.** This is the proposition that the continuous
Erdős minimum-overlap constant $C_{1b}$ satisfies $(4 - \sqrt{6})/5 \le C_{1b}$.

Source: Swierczkowski 1958; Optimization Problems, Constant 1b. -/
def lowerBound_S1958 : Prop := (4 - Real.sqrt 6) / 5 ≤ C₁ᵦ

private theorem sqrt6_lower : (2449 / 1000 : ℝ) ≤ Real.sqrt 6 := by
  apply Real.le_sqrt_of_sq_le
  norm_num

private theorem sqrt15_upper : Real.sqrt 15 ≤ (3873 / 1000 : ℝ) :=
  Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩

private theorem mid_le : (1551 / 5000 : ℝ) ≤ Real.sqrt (127 / 1000) := by
  apply Real.le_sqrt_of_sq_le
  norm_num

/-- **Świerczkowski's lower bound $C_{1b} \ge (4 - \sqrt{6})/5$.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $(4 - \sqrt{6})/5 \le C_{1b}$.

Source: Swierczkowski 1958 and Optimization Problems 1b. -/
public theorem lowerBound_S1958_holds : lowerBound_S1958 := by
  change (4 - Real.sqrt 6) / 5 ≤ C₁ᵦ
  have hM : Real.sqrt (4 - Real.sqrt 15) ≤ C₁ᵦ := lowerBound_M1959_holds
  refine le_trans ?_ hM
  have hLHS : (4 - Real.sqrt 6) / 5 ≤ 1551 / 5000 := by linarith [sqrt6_lower]
  have hinner : (127 / 1000 : ℝ) ≤ 4 - Real.sqrt 15 := by linarith [sqrt15_upper]
  have hmono : Real.sqrt (127 / 1000) ≤ Real.sqrt (4 - Real.sqrt 15) :=
    Real.sqrt_le_sqrt hinner
  exact hLHS.trans (mid_le.trans hmono)

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

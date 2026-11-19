/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.LeverageReturn
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Finance.LeverageReturn

open MathlibExt.Economics.Finance.LeverageReturn

example {rE : ℝ}
    (haccount : ((60 : ℝ) + 40) * (1 / 10) = 60 * rE + 40 * (1 / 20)) :
    rE = 2 / 15 := by
  have h := modiglianiMiller_II (E := 60) (D := 40) (rA := 1 / 10) (rD := 1 / 20)
    (rE := rE) (by norm_num) haccount
  norm_num at h
  exact h

example {rE : ℝ}
    (haccount : ((60 : ℝ) + 40) * (1 / 10) = 60 * (2 / 15) + 40 * (1 / 20))
    (hrE : rE = 2 / 15) :
    ((60 : ℝ) / 100) * rE + (40 / 100) * (1 / 20) = (1 / 10 : ℝ) := by
  have hV : (60 : ℝ) + 40 ≠ 0 := by norm_num
  rw [← hrE] at haccount
  have h := wacc_eq_assetReturn (E := 60) (D := 40) (rA := 1 / 10) (rD := 1 / 20)
    (rE := rE) hV haccount
  have h60 : ((60 : ℝ) + 40) = 100 := by norm_num
  rwa [h60] at h

example {E rA rD rE : ℝ} (hE : E ≠ 0)
    (haccount : (E + 0) * rA = E * rE + 0 * rD) : rE = rA := by
  have h := modiglianiMiller_II (D := 0) hE haccount
  simpa using h

end MathlibExtTest.Economics.Finance.LeverageReturn

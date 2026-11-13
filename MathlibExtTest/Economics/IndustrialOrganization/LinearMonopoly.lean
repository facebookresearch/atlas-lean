/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.IndustrialOrganization.LinearMonopoly
import Mathlib.Tactic

/-! Examples and checks for `MathlibExt.Economics.IndustrialOrganization.LinearMonopoly` (Atlas EC17.T02). -/

namespace MathlibExtTest.Economics.IndustrialOrganization.LinearMonopoly

open MathlibExt.Economics.LinearMonopoly
open MathlibExt.Economics.DeadweightLoss

/-- Test model: `a = 10`, `b = 1`, `c = 2`. -/
def testModel : Model where
  a := 10
  b := 1
  c := 2
  b_pos := by norm_num
  c_lt_a := by norm_num

example : monopolyQuantity testModel = 4 := by
  show ((10 - 2 : ℝ) / (2 * 1) = 4)
  norm_num

example : competitiveQuantity testModel = 8 := by
  show ((10 - 2 : ℝ) / 1 = 8)
  norm_num

example : inverseDemand testModel (monopolyQuantity testModel) = 6 := by
  rw [inverseDemand_monopolyQuantity]
  show ((10 + 2 : ℝ) / 2 = 6)
  norm_num

example : deadweightLoss (inverseDemand testModel) (fun _ => (2:ℝ))
    (competitiveQuantity testModel) (monopolyQuantity testModel) = 8 := by
  have h := deadweightLoss_monopoly testModel
  have hc : (fun _ : ℝ => (2:ℝ)) = (fun _ => testModel.c) := rfl
  rw [hc, h]
  show (((10 - 2 : ℝ) ^ 2 / (8 * 1)) = 8)
  norm_num

end MathlibExtTest.Economics.IndustrialOrganization.LinearMonopoly

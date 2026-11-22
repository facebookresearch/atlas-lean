/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.TwoStageNoiseBudget

@[expose] public section

open PhyslibExt.Communications.TwoStageNoiseBudget MeasureTheory ProbabilityTheory

namespace PhyslibExtTest.Communications.TwoStageNoiseBudget

/-- Concrete cascade: `G1 = 2`, `F1 = 2`, `F2 = 4` gives
`F = 2 + (4 - 1)/2 = 7/2` at the power level. -/
example : noiseFactor (2 * 3) (thermalNoisePower 1 1 1)
    (twoStageOutputNoisePower 2 3 (thermalNoisePower 1 1 1)
      (addedNoisePower 2 2 (thermalNoisePower 1 1 1))
      (addedNoisePower 3 4 (thermalNoisePower 1 1 1))) = 7 / 2 := by
  rw [noiseFactor_twoStageOutputNoisePower 1 1 1 2 3 2 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num

end PhyslibExtTest.Communications.TwoStageNoiseBudget

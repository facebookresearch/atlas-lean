/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairTwoCycleObstructionRepair
import Code.FrontierD.SixVertexWindingCycleBranchRecovery









namespace StatMech.FrontierD

noncomputable section



def sixVertexFourByTwoObstructionWindingTarget :
    SixVertexSignedWindingCycleTarget
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
      sixVertexFourByTwoBottomCycleFamily true where
  target := (sixVertexFourByTwoCycleMiddleFirst,
    sixVertexFourByTwoCycleMiddleSecond)
  horizontalDelta := by
    funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert
  verticalDelta := by
    funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByTwoBottomCycleFamily_nonzero :
    sixVertexFourByTwoBottomCycleFamily.horizontalFlow
      (sixVertexFourByTwoVertex 0 0) = 1 := by
  decide +revert


theorem sixVertexFourByTwoObstructionWindingTarget_ne_source :
    sixVertexFourByTwoObstructionWindingTarget.target ≠
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) := by
  exact SixVertexSignedWindingCycleTarget.target_ne_source_of_horizontalFlow_ne_zero
      sixVertexFourByTwoObstructionWindingTarget
      (sixVertexFourByTwoVertex 0 0) (by
        rw [sixVertexFourByTwoBottomCycleFamily_nonzero]
        norm_num)



theorem sixVertexFourByTwoObstructionWindingTarget_recovers :
    sixVertexFourByTwoObstructionWindingTarget.recover.target =
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) := rfl

end

end StatMech.FrontierD

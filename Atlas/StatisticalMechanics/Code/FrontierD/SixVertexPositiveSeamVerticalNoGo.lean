/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPositiveSeamWindingFlows
import Code.FrontierD.SixVertexFourByTwoTwoCycleHall











namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in


theorem sixVertexFourByTwo_no_positiveVerticalWindingTargetIndex
    (column : Fin sixVertexFourByTwoTorus.width)
    (target : Fin 28 × Fin 28) :
    ¬ (sixVertexPairUnionHorizontalDelta
          (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
          (sixVertexFourByTwoTargetIndexArrows target) =
        (sixVertexPositiveVerticalWindingFamily column).horizontalFlow ∧
      sixVertexPairUnionVerticalDelta
          (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
          (sixVertexFourByTwoTargetIndexArrows target) =
        (sixVertexPositiveVerticalWindingFamily column).verticalFlow) := by
  rcases target with ⟨first, second⟩
  fin_cases column <;> fin_cases first <;> fin_cases second <;>
    decide +revert

end

end StatMech.FrontierD

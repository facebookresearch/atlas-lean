/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorPair03Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorFiniteCoordinates

/-! Assemble every original incoming tensor coordinate from complete bounded certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original coordinate of pair 3 has the exact genuine normalization two. -/
theorem generatedRootEight_incoming_tensor_pair_03 : ∀ r n,
    generatedNinthLowerSpinTensorFourierInteger 0
      (generatedNinthLowerSpinTensorFourierInteger 1
        (generatedRootEightIncomingTensorStageInteger 3 r)) n =
      2 * generatedRootEightIncomingTensorStageInteger 4 r n := by
  intro r
  apply generatedRootEight_incoming_tensor_coordinate_cover
  intro b u
  exact generatedRootEight_incoming_tensor_pair_03_blocks b r u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

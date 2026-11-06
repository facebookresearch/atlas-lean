/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorPair01Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorFiniteCoordinates

/-! Assemble every original incoming tensor coordinate from complete bounded certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original coordinate of pair 1 has the exact genuine normalization two. -/
theorem generatedRootEight_incoming_tensor_pair_01 : ∀ r n,
    generatedNinthLowerSpinTensorFourierInteger 4
      (generatedNinthLowerSpinTensorFourierInteger 5
        (generatedRootEightIncomingTensorStageInteger 1 r)) n =
      2 * generatedRootEightIncomingTensorStageInteger 2 r n := by
  intro r
  apply generatedRootEight_incoming_tensor_coordinate_cover
  intro b u
  exact generatedRootEight_incoming_tensor_pair_01_blocks b r u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

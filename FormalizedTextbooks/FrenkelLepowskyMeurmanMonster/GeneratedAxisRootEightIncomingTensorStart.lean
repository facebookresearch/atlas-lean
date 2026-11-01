/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorStartCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorFiniteCoordinates

/-! Assemble every original incoming tensor coordinate from complete bounded certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Stage zero is exactly sixteen times the genuine full source pre action. -/
theorem generatedRootEight_incoming_tensor_start : ∀ r n,
    generatedRootEightIncomingTensorStageInteger 0 r n =
      16 * generatedRootEightIncomingTensorPreInteger
        (generatedRootEightIncomingTensorSourceCache r) n := by
  intro r
  apply generatedRootEight_incoming_tensor_coordinate_cover
  intro b u
  exact generatedRootEight_incoming_tensor_start_blocks b r u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

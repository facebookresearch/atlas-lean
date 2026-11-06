/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorStartCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorFiniteCoordinates

/-! Every canonical source coordinate is initialized by the complete original final tensor numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The genuine canonical pre action starts from all original final tensor coordinates. -/
theorem generatedRootEight_canonical_tensor_start : ∀ r n,
    generatedRootEightCanonicalTensorStageInteger 0 r n =
      16 * generatedRootEightCanonicalTensorPreInteger
        (fun z => generatedRootEightPositiveFinalTensorNumerator z r) n := by
  intro r
  apply generatedRootEight_incoming_tensor_coordinate_cover
  intro b u
  exact generatedRootEight_canonical_tensor_start_blocks b r u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

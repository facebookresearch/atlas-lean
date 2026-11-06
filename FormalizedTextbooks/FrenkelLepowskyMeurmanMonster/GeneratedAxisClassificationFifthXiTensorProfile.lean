/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorAction

/-! A bounded first support-coordinate check for the actual Q-corrected Xi candidate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check one genuine support address before expanding the certificate scope.
/-- The actual signed Xi tensor numerator fixes the first original support coordinate. -/
theorem generatedFifth_xi_tensor_first_coordinate :
    generatedFifthXiCorrectedTensorNumerator (generatedFifthXiTensorAddress 0 0)
      (generatedFifthOddRootOutputData 0).2 = 16 * generatedFifthXiTensorWeight 0 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

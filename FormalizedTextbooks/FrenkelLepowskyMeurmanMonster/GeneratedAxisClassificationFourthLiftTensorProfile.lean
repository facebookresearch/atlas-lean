/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftIntegerOperators

/-! A first bounded support-coordinate certificate for the actual corrected lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- This checks one genuine support address before increasing the certificate's scope.
/-- The actual full signed integer operator fixes the first original support address. -/
theorem generatedFourth_lift_tensor_first_coordinate :
    generatedFourthLiftCorrectedTensorNumerator (generatedFourthLiftSupportAddress 0 0)
      (generatedFourthQAffineTensorColumns 0) =
    64 * generatedFourthLiftIntegerTensor (generatedFourthLiftSupportAddress 0 0)
      (generatedFourthQAffineTensorColumns 0) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

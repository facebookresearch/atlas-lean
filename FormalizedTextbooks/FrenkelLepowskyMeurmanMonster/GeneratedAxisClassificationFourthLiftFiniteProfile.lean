/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftFiniteKernel

/-! A bounded first-coordinate check of the exact sparse corrected tensor operator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- The exact finite sparse coordinate includes both Fourier changes and all original phases.
/-- A kernel check includes every genuine phase at the first original tensor support point. -/
theorem generatedFourth_lift_sparse_first_coordinate :
    generatedFourthLiftSparseCorrectedFast (generatedFourthLiftSupportAddress 0 0)
      (generatedFourthQAffineTensorColumns 0) =
        64 * generatedFourthLiftIntegerTensor (generatedFourthLiftSupportAddress 0 0)
          (generatedFourthQAffineTensorColumns 0) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

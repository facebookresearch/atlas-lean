/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftFiniteKernel

/-! Bounded exact support certificate block 1 for the genuine corrected flag tensor. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 40000000 in
-- Check twenty-eight actual support points, including every original quadratic and central phase.
/-- Exact corrected tensor coordinates for actual families 7 through 13. -/
theorem generatedFourth_lift_tensor_certificate_1 :
    ∀ k : Fin 7, ∀ s : Fin 4,
      let r : Fin 28 := ⟨7 + k.val, by omega⟩
      generatedFourthLiftSparseCorrectedFast (generatedFourthLiftSupportAddress r s)
        (generatedFourthQAffineTensorColumns r) =
          64 * generatedFourthLiftIntegerTensor (generatedFourthLiftSupportAddress r s)
            (generatedFourthQAffineTensorColumns r) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

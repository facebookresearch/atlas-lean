/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorAction

/-! Sixteen actual support-coordinate checks for the signed Xi tensor candidate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 240000000 in
-- Check eight original dictionary rows and both genuine all-one spin addresses.
/-- The actual signed Xi numerator fixes original tensor rows 0 through 7. -/
theorem generatedFifth_xi_tensor_certificate0 : ∀ k : Fin 8, ∀ h : ZMod 2,
    generatedFifthXiCorrectedTensorNumerator
      (generatedFifthXiTensorAddress ⟨0 + k.val, by omega⟩ h)
      (generatedFifthOddRootOutputData ⟨0 + k.val, by omega⟩).2 =
        16 * generatedFifthXiTensorWeight ⟨0 + k.val, by omega⟩ h := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

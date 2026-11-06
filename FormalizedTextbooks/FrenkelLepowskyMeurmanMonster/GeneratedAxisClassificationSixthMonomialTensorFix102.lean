/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialMaskSoundness

/-! Complete original corrected tensor fixation on a bounded block of source spin labels. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 8000000 in
-- Check all twenty-four physical coordinates on 256 source labels with complete signed action.
/-- Every original corrected tensor coordinate in this finite block is fixed. -/
theorem generatedSixth_monomial_tensor_fix102 : ∀ n : Fin 256, ∀ i : Fin 24,
    generatedSixthMonomialFastTensor 1 ⟨512 + n.val, by omega⟩ i =
      generatedSixthTensorExecutable ⟨512 + n.val, by omega⟩ i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

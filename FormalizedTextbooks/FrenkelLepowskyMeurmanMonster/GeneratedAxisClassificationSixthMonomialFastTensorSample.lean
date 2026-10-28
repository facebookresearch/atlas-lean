/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialMaskSoundness

/-! A bounded complete original corrected tensor check by exact bit-parity arithmetic. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Check full preferred signs and all twenty-four spatial coordinates on sixty-four labels.
/-- Every complete signed original corrected tensor coordinate in this bounded sample agrees. -/
theorem generatedSixth_monomial_fast_tensor_sample : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedSixthMonomialFastTensor 0 ⟨n.val, by omega⟩ i =
      generatedSixthTensorExecutable ⟨n.val, by omega⟩ i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

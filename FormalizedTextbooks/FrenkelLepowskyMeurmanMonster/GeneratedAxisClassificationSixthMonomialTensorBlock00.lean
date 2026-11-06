/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorData

/-! A bounded complete tensor-coordinate check for the first corrected original monomial. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 8000000 in
-- Check sixty-four original spin labels against every one of the twenty-four spatial coordinates.
/-- Every corrected coordinate in this original sixty-four-label block agrees exactly. -/
theorem generatedSixth_monomial_tensor_block00 : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedSixthMonomialTensorExecutable 0 ⟨n.val, by omega⟩ i =
      generatedSixthTensorExecutable ⟨n.val, by omega⟩ i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

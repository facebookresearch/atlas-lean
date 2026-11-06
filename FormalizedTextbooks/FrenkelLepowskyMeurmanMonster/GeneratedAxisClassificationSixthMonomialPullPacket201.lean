/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPullData

/-! Complete original affine labels and phases on 256 actual spin coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Check both full original affine pullback and central/quadratic phase on 256 coordinates.
/-- Every cached affine address and preferred sign agrees with the original expression. -/
theorem generatedSixth_monomial_pull_packet2_01 : ∀ n : Fin 256,
    generatedSixthMonomialPullLabel 2 ⟨256 + n.val, by omega⟩ =
      generatedSixthMonomialOriginalPull 2 ⟨256 + n.val, by omega⟩ ∧
    generatedSixthMonomialPullPhase 2 ⟨256 + n.val, by omega⟩ =
      generatedSixthMonomialOriginalPhase 2 ⟨256 + n.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

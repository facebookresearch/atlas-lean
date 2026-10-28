/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaData

/-! Exact original diagonal Gaussian signs on a bounded spin-address block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Check 256 actual diagonal Gaussian signs, with all six original cocode characters.
/-- The bounded cache agrees with the original diagonal Gaussian. -/
theorem generatedSixth_spin_gamma_packet_02 : ∀ n : Fin 256,
    generatedSixthSpinGammaFast ⟨512 + n.val, by omega⟩ =
      nortonUIntegerGammaSign (golayLabelCoefficients ⟨512 + n.val, by omega⟩) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

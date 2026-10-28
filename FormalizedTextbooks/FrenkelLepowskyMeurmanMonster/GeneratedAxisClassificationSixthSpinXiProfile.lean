/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaCertified

/-! A bounded initial check of the genuine 64-term Gaussian spin recurrence. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Sixty-four rows of the actual first Gaussian recurrence, with all original signs retained.
/-- The first sixty-four Gaussian rows match the signed integral cache. -/
theorem generatedSixth_spin_xi_profile : ∀ n : Fin 64,
    generatedSixthIntegerXiCached (generatedSixthSpinData 1) ⟨n.val, by omega⟩ =
      generatedSixthSpinData 2 ⟨n.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

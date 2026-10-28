/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddSupportData

/-! Bounded original signed spin addresses give complete odd-short support coverage. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check 512 original code addresses and both original Omega-related spin coefficients.
/-- Every nonzero original spin-pair sum has its genuine displayed code owner. -/
theorem generatedSixth_monomial_odd_owner2 :
    ∀ d : Fin 512,
      generatedSixthPackedSpinPhase (Fin.ofNat 4096 (2 * 512 + d.val)) +
        generatedSixthPackedSpinPhase (Fin.ofNat 4096 (2 * 512 + d.val + 2048)) = 0 ∨
      generatedSixthMonomialOddCode
        (generatedSixthMonomialOddOwner (Fin.ofNat 2048 (2 * 512 + d.val))) =
          Fin.ofNat 2048 (2 * 512 + d.val) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePackedData

/-! Bounded original signed spin coordinates in block 1. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 8000000 in
-- Check exactly 256 original signed coordinates against the genuine affine phase formula.
/-- Every phase in original block 1 agrees with the proved actual Pauli phase formula. -/
theorem generatedSixth_packed_spin_phase_block01 : ∀ j : Fin 256,
    generatedSixthPackedSpinPhase ⟨256 + j.val, by omega⟩ =
      generatedSixthPackedPhaseFormula ⟨256 + j.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

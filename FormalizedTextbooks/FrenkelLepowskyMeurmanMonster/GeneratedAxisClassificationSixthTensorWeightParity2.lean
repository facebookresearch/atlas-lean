/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorWeightParityData

/-! A bounded comparison retains the original full physical-code weight sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 8000000 in
-- Check 256 actual Golay code weights against the displayed parity bits.
/-- Every weight-sign bit in this bounded original code interval is genuine. -/
theorem generatedSixth_tensor_weight_parity2 : ∀ d : Fin 256,
    generatedSixthTensorWeightParity (Fin.ofNat 2048 (2 * 256 + d.val)) =
      (golayMaskWeight (golayEncodedMask (2 * 256 + d.val)) / 4 : ℕ) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortPacket31Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortTransport

/-! A bounded packet of the full actual corrected-Xi preferred-Q phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check 64 actual central coefficients and the Q-correction characters.
/-- Every displayed phase is the genuine full preferred-Q phase. -/
theorem generatedFifthXiShortPacket31_phase : ∀ e : Fin 64,
    generatedFifthXiEvenShortPhase
      (generatedFifthXiShortCachedEven (generatedFifthXiShortPacket31Source e))
      (generatedFifthXiShortCachedEven (generatedFifthXiShortPacket31Target e)) =
      generatedFifthXiShortPacket31Phase e := by
  intro e
  unfold generatedFifthXiEvenShortPhase
  rw [← generatedFifthXiShortCachedQ_actual, ← generatedFifthXiShortCachedQ_actual]
  revert e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

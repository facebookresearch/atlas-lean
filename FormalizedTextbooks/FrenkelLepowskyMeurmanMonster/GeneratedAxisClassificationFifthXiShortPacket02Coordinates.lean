/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortPacket02Phase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortCertified
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortNumerator

/-! Exact coefficient preservation for a bounded packet of genuine corrected-Xi short images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each checked physical image differs from the preferred representative only by sign. -/
theorem generatedFifthXiShortPacket02_sign : ∀ e : Fin 64,
    generatedFifthXiShortPacket02Sign e = 1 ∨ generatedFifthXiShortPacket02Sign e = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check the actual signed integer coefficient equation on every row in this packet.
/-- The full corrected preferred-Q phases preserve the original short coefficient numerators. -/
theorem generatedFifthXiShortPacket02_coefficient : ∀ e : Fin 64,
    (if generatedFifthXiShortPacket02Phase e = 0 then (1 : ℤ) else -1) *
        generatedFifthXiShortCachedNumerator (generatedFifthXiShortPacket02Source e) =
      generatedFifthXiShortCachedNumerator (generatedFifthXiShortPacket02Target e) := by
  decide +kernel

/-- Every original target coordinate in this packet is fixed by the genuine corrected-Xi action. -/
theorem generatedFifthXiShortPacket02_fixed (e : Fin 64) :
    localShortOperator generatedFifthXiCorrectedFiber
        (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven (generatedFifthXiShortPacket02Target e))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven (generatedFifthXiShortPacket02Target e))) := by
  rw [generatedFifthXiShortCached_operator
    (generatedFifthXiShortPacket02Source e) (generatedFifthXiShortPacket02Target e)
    (generatedFifthXiShortPacket02Sign e) (generatedFifthXiShortPacket02_sign e)
    (generatedFifthXiShortPacket02_physical e)
    (generatedFifthXiShortPacket02Phase e) (generatedFifthXiShortPacket02_phase e)]
  exact generatedFifthXiShortCachedNumerator_signed _ _ _
    (generatedFifthXiShortPacket02_coefficient e)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

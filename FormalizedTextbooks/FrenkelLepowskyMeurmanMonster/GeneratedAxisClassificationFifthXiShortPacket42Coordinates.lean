/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortPacket42Phase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortCertified
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortNumerator

/-! Exact coefficient preservation for a bounded packet of genuine corrected-Xi short images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each checked physical image differs from the preferred representative only by sign. -/
theorem generatedFifthXiShortPacket42_sign : ∀ e : Fin 64,
    generatedFifthXiShortPacket42Sign e = 1 ∨ generatedFifthXiShortPacket42Sign e = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check the actual signed integer coefficient equation on every row in this packet.
/-- The full corrected preferred-Q phases preserve the original short coefficient numerators. -/
theorem generatedFifthXiShortPacket42_coefficient : ∀ e : Fin 64,
    (if generatedFifthXiShortPacket42Phase e = 0 then (1 : ℤ) else -1) *
        generatedFifthXiShortCachedNumerator (generatedFifthXiShortPacket42Source e) =
      generatedFifthXiShortCachedNumerator (generatedFifthXiShortPacket42Target e) := by
  decide +kernel

/-- Every original target coordinate in this packet is fixed by the genuine corrected-Xi action. -/
theorem generatedFifthXiShortPacket42_fixed (e : Fin 64) :
    localShortOperator generatedFifthXiCorrectedFiber
        (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven (generatedFifthXiShortPacket42Target e))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven (generatedFifthXiShortPacket42Target e))) := by
  rw [generatedFifthXiShortCached_operator
    (generatedFifthXiShortPacket42Source e) (generatedFifthXiShortPacket42Target e)
    (generatedFifthXiShortPacket42Sign e) (generatedFifthXiShortPacket42_sign e)
    (generatedFifthXiShortPacket42_physical e)
    (generatedFifthXiShortPacket42Phase e) (generatedFifthXiShortPacket42_phase e)]
  exact generatedFifthXiShortCachedNumerator_signed _ _ _
    (generatedFifthXiShortPacket42_coefficient e)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

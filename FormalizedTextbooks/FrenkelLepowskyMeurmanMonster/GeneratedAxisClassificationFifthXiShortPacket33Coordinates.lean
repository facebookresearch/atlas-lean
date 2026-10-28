/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortPacket33Phase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortCertified
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortNumerator

/-! Exact coefficient preservation for a bounded packet of genuine corrected-Xi short images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each checked physical image differs from the preferred representative only by sign. -/
theorem generatedFifthXiShortPacket33_sign : ∀ e : Fin 64,
    generatedFifthXiShortPacket33Sign e = 1 ∨ generatedFifthXiShortPacket33Sign e = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check the actual signed integer coefficient equation on every row in this packet.
/-- The full corrected preferred-Q phases preserve the original short coefficient numerators. -/
theorem generatedFifthXiShortPacket33_coefficient : ∀ e : Fin 64,
    (if generatedFifthXiShortPacket33Phase e = 0 then (1 : ℤ) else -1) *
        generatedFifthXiShortCachedNumerator (generatedFifthXiShortPacket33Source e) =
      generatedFifthXiShortCachedNumerator (generatedFifthXiShortPacket33Target e) := by
  decide +kernel

/-- Every original target coordinate in this packet is fixed by the genuine corrected-Xi action. -/
theorem generatedFifthXiShortPacket33_fixed (e : Fin 64) :
    localShortOperator generatedFifthXiCorrectedFiber
        (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven (generatedFifthXiShortPacket33Target e))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven (generatedFifthXiShortPacket33Target e))) := by
  rw [generatedFifthXiShortCached_operator
    (generatedFifthXiShortPacket33Source e) (generatedFifthXiShortPacket33Target e)
    (generatedFifthXiShortPacket33Sign e) (generatedFifthXiShortPacket33_sign e)
    (generatedFifthXiShortPacket33_physical e)
    (generatedFifthXiShortPacket33Phase e) (generatedFifthXiShortPacket33_phase e)]
  exact generatedFifthXiShortCachedNumerator_signed _ _ _
    (generatedFifthXiShortPacket33_coefficient e)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

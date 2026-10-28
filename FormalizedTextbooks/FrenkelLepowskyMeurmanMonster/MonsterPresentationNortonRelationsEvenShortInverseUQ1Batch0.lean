/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual inverse-U images for the second preferred basis packet, retaining complete Q phases. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseShortInput

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Evaluate every binary coordinate and the actual preferred-lift central correction.
/-- Sixteen entire genuine inverse-U images in the second basis unit's Fourier packet. -/
theorem monsterNortonEvenShortInverseUQ1_batch0 (e : Fin 16) :
    monsterNortonUQInverseFastImage
      (monsterNortonShortQ (monsterNortonEvenShortInverseUInput 1
        ⟨0 + e.val, by omega⟩)) =
      qCentral (monsterNortonEvenShortInverseUPhase 1 ⟨0 + e.val, by omega⟩) *
        monsterNortonShortQ (monsterNortonEvenShortInverseUOutput 1
          ⟨0 + e.val, by omega⟩) := by
  unfold monsterNortonShortQ
  rw [monsterNortonEvenShortInverseUInputIntegral_actual,
    monsterNortonEvenShortInverseUIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · funext i
    revert e i
    decide +kernel
  · revert e
    decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

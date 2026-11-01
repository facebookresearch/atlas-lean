/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual inverse Norton short images, batch 7. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCacheInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- This checks 128 complete binary images and their genuine central signs.
/-- Each finite image agrees with the proved actual inverse Norton Q action. -/
theorem monsterNortonLine01ShortInverse_certificate_7 (a : Fin 8) (k : Fin 16) :
    monsterNortonUQInverseFastImage (monsterNortonShortQSource (Sum.inr (Sum.inr
      (monsterNortonLine01ShortInputCode (monsterNortonLine01ShortInverseBatchIndex 7 a),
        monsterNortonLine01ShortPhysicalColumn k)))) =
      qCentral (monsterNortonLine01ShortInversePhase
        (monsterNortonLine01ShortInverseBatchIndex 7 a) k) *
          monsterNortonLine01ShortInverseOutputQ
            (monsterNortonLine01ShortInverseBatchIndex 7 a) k := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    revert a k
    decide +kernel
  · apply toAdd.injective
    revert a k
    decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

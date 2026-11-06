/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A full-phase finite squared-U certificate on 128 genuine middle short labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02FirstU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 128000000 in
-- Check all binary coordinates and central coefficients of the 128 full Q images.
/-- The actual full-phase squared-U evaluator reverses these exact middle short entries. -/
theorem monsterNortonLine02MiddleShortQ_certificate2 (a : Fin 2) (e : Fin 64) :
    monsterNortonLine02QFastImage
      (monsterNortonLine02MiddleOutputQ (Fin.natAdd 4 (Fin.castAdd 2 a)) e) =
      qCentral (monsterNortonLine02MiddlePhase (Fin.natAdd 4 (Fin.castAdd 2 a)) e) *
        monsterNortonLine02MiddleInputQ (Fin.natAdd 4 (Fin.castAdd 2 a)) e := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    revert a e j
    decide +kernel
  · apply toAdd.injective
    revert a e
    decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

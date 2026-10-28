/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual input labels of the reached octad packet for inverse Norton U. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCacheInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original octad1281 label for each reached even sign. -/
noncomputable def monsterNortonLine01PairInverseShortInput (e : Fin 64) : GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonOctadIndex 1281 monsterNortonLine01PairUOctad_weight, e))

/-- The finite physical integer formula for each input shortest vector. -/
def monsterNortonLine01PairInverseInputIntegral (e : Fin 64) : Fin 24 → ℤ :=
  monsterNortonOctadIntegral 1281 monsterNortonLine01PairUOctadPositions e

/-- Every input formula agrees with the actual Conway short dictionary. -/
theorem monsterNortonLine01PairInverseInputIntegral_actual (e : Fin 64) :
    griessShortIntegral (monsterNortonLine01PairInverseShortInput e) =
      monsterNortonLine01PairInverseInputIntegral e :=
  monsterNortonOctadIntegral_eq (1281 : Fin 4096) monsterNortonLine01PairUOctad_weight
    monsterNortonLine01PairUOctadPositions monsterNortonLine01PairUOctad_coordinate e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded kernel certificate for actual inverse-U input lattice-coordinate parity. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUInputParityData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check at most four octad families against the actual integer Leech coordinate map.
/-- Every displayed parity bit is the genuine lattice-coordinate parity of this input. -/
theorem monsterNortonEvenShortInverseUInputParityBatch2_actual
    (k : Fin 4) (e : Fin 64) (i : Fin 24) :
    integerParity (monsterNortonLeechCoordinates
      (monsterNortonEvenShortInverseUInputIntegral ⟨8 + k.val, by omega⟩ e)) i =
        (if (monsterNortonEvenShortInverseUInputParityMask
          ⟨8 + k.val, by omega⟩ e).testBit i.val then 1 else 0) := by
  revert k e i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

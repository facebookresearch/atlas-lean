/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Assembled exact lattice-coordinate parity of every reached inverse-U octad input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUInputParityBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUInputParityBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUInputParityBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUInputParityBatch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUInputParityBatch4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUInputParityBatch5

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every parity mask is the actual lattice-coordinate parity of its original short input. -/
theorem monsterNortonEvenShortInverseUInputParity_actual
    (k : Fin 23) (e : Fin 64) (i : Fin 24) :
    integerParity (monsterNortonLeechCoordinates
      (monsterNortonEvenShortInverseUInputIntegral k e)) i =
        (if (monsterNortonEvenShortInverseUInputParityMask k e).testBit i.val then 1 else 0) := by
  fin_cases k
  · exact monsterNortonEvenShortInverseUInputParityBatch0_actual 0 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch0_actual 1 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch0_actual 2 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch0_actual 3 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch1_actual 0 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch1_actual 1 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch1_actual 2 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch1_actual 3 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch2_actual 0 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch2_actual 1 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch2_actual 2 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch2_actual 3 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch3_actual 0 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch3_actual 1 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch3_actual 2 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch3_actual 3 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch4_actual 0 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch4_actual 1 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch4_actual 2 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch4_actual 3 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch5_actual 0 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch5_actual 1 e i
  · exact monsterNortonEvenShortInverseUInputParityBatch5_actual 2 e i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

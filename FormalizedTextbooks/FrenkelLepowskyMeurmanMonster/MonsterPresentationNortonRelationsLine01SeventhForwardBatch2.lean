/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact inverse checks binding the proposed packets to the actual seventh tensor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhForwardData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactColumnInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Check one fixed physical packet using the exact sixty-four-term inverse operator.
private theorem inverse_column8 (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket 8)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup 8 p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check one fixed physical packet using the exact sixty-four-term inverse operator.
private theorem inverse_column9 (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket 9)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup 9 p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check one fixed physical packet using the exact sixty-four-term inverse operator.
private theorem inverse_column10 (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket 10)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup 10 p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check one fixed physical packet using the exact sixty-four-term inverse operator.
private theorem inverse_column11 (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket 11)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup 11 p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

/-- Batch 2 of the exact actual inverse packet checks. -/
theorem monsterNortonLine01SeventhForward_inverse_batch2 (i : Fin 4) (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator
      (monsterNortonLine01SeventhForwardPacket ⟨8 + i.val, by omega⟩)
        (monsterNortonLine01TensorSpinLabel p) =
          -monsterNortonLine01TensorSeventhCoefficientLookup ⟨8 + i.val, by omega⟩ p := by
  fin_cases i
  · exact inverse_column8 p
  · exact inverse_column9 p
  · exact inverse_column10 p
  · exact inverse_column11 p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

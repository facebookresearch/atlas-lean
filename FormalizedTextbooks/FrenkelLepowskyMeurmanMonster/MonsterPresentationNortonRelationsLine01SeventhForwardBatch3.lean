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
private theorem inverse_column12 (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket 12)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup 12 p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check one fixed physical packet using the exact sixty-four-term inverse operator.
private theorem inverse_column13 (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket 13)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup 13 p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check one fixed physical packet using the exact sixty-four-term inverse operator.
private theorem inverse_column14 (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket 14)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup 14 p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check one fixed physical packet using the exact sixty-four-term inverse operator.
private theorem inverse_column15 (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket 15)
      (monsterNortonLine01TensorSpinLabel p) =
        -monsterNortonLine01TensorSeventhCoefficientLookup 15 p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

/-- Batch 3 of the exact actual inverse packet checks. -/
theorem monsterNortonLine01SeventhForward_inverse_batch3 (i : Fin 4) (p : Fin 128) :
    8 * monsterNortonUCompactInverseNumerator
      (monsterNortonLine01SeventhForwardPacket ⟨12 + i.val, by omega⟩)
        (monsterNortonLine01TensorSpinLabel p) =
          -monsterNortonLine01TensorSeventhCoefficientLookup ⟨12 + i.val, by omega⟩ p := by
  fin_cases i
  · exact inverse_column12 p
  · exact inverse_column13 p
  · exact inverse_column14 p
  · exact inverse_column15 p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

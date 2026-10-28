/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete matrix, pair, and octad vanishing at the actual eleventh word step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorInverseTrialityOctadZero

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual eleventh-state physical matrix coordinate vanishes. -/
theorem monsterNortonLine01Eleventh_matrix_zero (i j : Fin 24) :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).1 i j = 0 := by
  exact monsterNortonTensor_extra_inverse_matrix_zero _
    monsterNortonLine01SeventhU_matrix_zero monsterNortonLine01SeventhU_pair_zero i j

/-- Every actual eleventh-state pair-short coordinate vanishes. -/
theorem monsterNortonLine01Eleventh_pair_zero (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).2.1
        (Sum.inl (s, p)) = 0 := by
  exact monsterNortonTensor_extra_inverse_pair_short_zero _
    monsterNortonLine01SeventhU_matrix_zero monsterNortonLine01SeventhU_pair_zero s p

/-- Every actual eleventh-state octad-short coordinate vanishes. -/
theorem monsterNortonLine01Eleventh_octad_zero (d : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).2.1
        (Sum.inr (Sum.inl (d, e))) = 0 := by
  exact monsterNortonTensor_extra_inverse_octad_zero _
    monsterNortonLine01SeventhU_octad_zero d e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

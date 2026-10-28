/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete coordinate state after the seventh literal first-line word step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSixthAntisymmetric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01MatrixSixthCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityFullCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact seventh short state, supported entirely on the original octad blocks. -/
noncomputable def monsterNortonLine01ShortSeventhCoordinates : GriessShortIndex → ℝ
  | Sum.inr (Sum.inl (d, e)) => trialityOctadAction (fun r =>
      monsterNortonShortProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV
        (Sum.inr (Sum.inl (d, r)))) e
  | _ => 0

/-- The exact seventh tensor state in the original physical-coordinate formula. -/
noncomputable def monsterNortonLine01TensorSeventhCoordinates : SpinIndex → Fin 24 → ℝ :=
  monsterNortonTensorTrialityCoordinates
    (monsterNortonShortProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)
    (monsterNortonTensorProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)

/-- The complete coordinate Griess vector at the seventh literal step. -/
noncomputable def monsterNortonLine01TensorAfterVUExtraInverseVInverseUVExtra : GriessSpace :=
  griessConwayDecode (0,
    (monsterNortonLine01ShortSeventhCoordinates, monsterNortonLine01TensorSeventhCoordinates))

/-- The entire actual seventh Griess vector has no matrix, pair-short, or odd-short row. -/
theorem monsterNortonLine01TensorSeventh_actual :
    sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV =
      monsterNortonLine01TensorAfterVUExtraInverseVInverseUVExtra := by
  calc
    _ = griessConwayDecode (griessConwayEncode
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)) :=
        (griessConwayDecode_encode _).symm
    _ = _ := by
      apply congrArg griessConwayDecode
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · ext i j
        exact monsterNortonLine01MatrixSeventh_zero i j
      · funext r
        rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, i⟩)
        · exact monsterNortonLine01PairSeventh_zero s p
        · exact monsterNortonLine01ShortSeventh_octad_coordinates d e
        · exact monsterNortonLine01TensorSeventh_odd_short_zero d i
      · funext t i
        exact monsterNortonTensorTrialityCoordinates_actual _ t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

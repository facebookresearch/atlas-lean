/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete short and tensor pairings of the source odd and octad positive-triality packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortExtraPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorCoordinatePairing

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A whole octad Fourier packet has every physical tensor pairing zero. -/
theorem monsterNortonOctadExtra_tensor_form (d : Fin 759) (e : Fin 64)
    (t : SpinIndex) (j : Fin 24) :
    griessForm (monsterNortonShortExtraPacket (Sum.inr (Sum.inl (d, e))))
      (monsterNortonTensorUnit t j) = 0 := by
  rw [monsterNortonForm_tensorUnit_right, monsterNortonShortExtraPacket]
  change (griessConwayEncode (griessConwayDecode (0,
    (monsterNortonOctadShortCoordinates d (trialityOctadAction (Pi.single e 1)), 0)))).2.2 t j = 0
  rw [griessConwayEncode_decode _ (by intros; rfl)]
  rfl

/-- A whole source Y packet is orthogonal to every actual preferred short unit. -/
theorem monsterNortonOddExtra_short_form (d : Fin 2048) (i : Fin 24)
    (r : GriessShortIndex) :
    griessForm (monsterNortonShortExtraPacket (Sum.inr (Sum.inr (d, i))))
      (monsterNortonPureShort r) = 0 := by
  rw [monsterNortonShortExtraPacket, monsterNortonSourceY_tensor_column,
    monsterNortonTensorLift_short_form]

/-- Every physical tensor pairing of a whole source Y packet has its exact two-half sign. -/
theorem monsterNortonOddExtra_tensor_form (d : Fin 2048) (i : Fin 24)
    (t : SpinIndex) (j : Fin 24) :
    griessForm (monsterNortonShortExtraPacket (Sum.inr (Sum.inr (d, i))))
      (monsterNortonTensorUnit t j) =
        if j = i ∧ spinDictionaryCode t = d then
          qSign (t 11) *
            (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) / Real.sqrt 2
        else 0 := by
  rw [monsterNortonShortExtraPacket, monsterNortonSourceY_tensor_column,
    monsterNortonForm_tensorUnit_right, monsterNortonTensorLift_apply,
    griessConwayEncode_decode _ (by intros; rfl)]
  by_cases hj : j = i <;> by_cases hd : spinDictionaryCode t = d <;>
    simp [conwaySpinColumn, trialityYSpin, hj, hd]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

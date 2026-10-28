/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The entire actual second-input forward half equals its sparse norm-one source packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfPairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The seven literal actual generators preceding the final V in the first line word. -/
noncomputable def monsterNortonSecondForwardHalf : G :=
  extraIntoGenerated * y555NortonV * y555NortonActualU⁻¹ * y555NortonV *
    extraIntoGenerated⁻¹ * y555NortonActualU * y555NortonV

private theorem candidate_pairing (i : NortonSecondHalfIndex) :
    griessForm monsterNortonSecondHalfPacket (monsterNortonSecondHalfVector i) =
      monsterNortonSecondHalfCoefficient i * monsterNortonSecondHalfWeight i := by
  unfold monsterNortonSecondHalfPacket
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    monsterNortonSecondHalfVector_gram, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem candidate_sum_right (x : GriessSpace) :
    griessForm x monsterNortonSecondHalfPacket =
      ∑ i : NortonSecondHalfIndex, monsterNortonSecondHalfCoefficient i *
        griessForm x (monsterNortonSecondHalfVector i) := by
  rw [monsterNortonSecondHalfPacket, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Positive definiteness binds every coordinate of the entire actual forward half to the packet. -/
theorem monsterNortonEvenShortSecondHalf_actual :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 1)))))))) =
      monsterNortonSecondHalfPacket := by
  have h := monsterNortonGenerated_image_of_pairing monsterNortonSecondForwardHalf
    (monsterNortonPureShort (monsterNortonEvenShortBasis 1)) monsterNortonSecondHalfPacket
  apply h
  · change griessForm
      (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
        (y555NortonActualU.val (y555NortonV.val
          (monsterNortonPureShort (monsterNortonEvenShortBasis 1))))))))) _ = _
    rw [monsterNortonEvenShortSecondFirstSeven_actual, monsterNortonPureShort_form]
    simp only [ite_true]
    calc
      _ = griessForm monsterNortonSecondHalfPacket monsterNortonSecondHalfPacket := by
        rw [candidate_sum_right, candidate_sum_right]
        apply Finset.sum_congr rfl
        intro i _
        rw [monsterNortonSecondHalfPairings_actual, candidate_pairing]
      _ = 1 := monsterNortonSecondHalfPacket_norm
  · rw [monsterNortonSecondHalfPacket_norm, monsterNortonPureShort_form]
    simp only [ite_true]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

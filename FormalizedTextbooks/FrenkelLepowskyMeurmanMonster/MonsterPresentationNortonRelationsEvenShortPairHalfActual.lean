/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Positive definiteness identifies twelve complete literal forward-half images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem candidate_pairing (k : Fin 12) (i : NortonPairHalfIndex) :
    griessForm (monsterNortonPairHalfPacket k) (monsterNortonPairHalfVector k i) =
      monsterNortonPairHalfCoefficient k i * monsterNortonPairHalfWeight i := by
  unfold monsterNortonPairHalfPacket
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    monsterNortonPairHalfVector_gram, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem candidate_sum_right (k : Fin 12) (x : GriessSpace) :
    griessForm x (monsterNortonPairHalfPacket k) =
      ∑ i : NortonPairHalfIndex, monsterNortonPairHalfCoefficient k i *
        griessForm x (monsterNortonPairHalfVector k i) := by
  rw [monsterNortonPairHalfPacket, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Each whole literal forward-half image is its actual norm-one sparse packet, in every block. -/
theorem monsterNortonEvenShortPairHalf_actual (k : Fin 12) :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis
          (monsterNortonPairHalfBasisIndex k))))))))) =
      monsterNortonPairHalfPacket k := by
  have h := monsterNortonGenerated_image_of_pairing monsterNortonSecondForwardHalf
    (monsterNortonPureShort (monsterNortonEvenShortBasis (monsterNortonPairHalfBasisIndex k)))
      (monsterNortonPairHalfPacket k)
  apply h
  · change griessForm
      (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
        (y555NortonActualU.val (y555NortonV.val
          (monsterNortonPureShort (monsterNortonEvenShortBasis
            (monsterNortonPairHalfBasisIndex k)))))))))) _ = _
    rw [monsterNortonEvenShortFirstSeven_actual, monsterNortonPureShort_form]
    simp only [ite_true]
    calc
      _ = griessForm (monsterNortonPairHalfPacket k) (monsterNortonPairHalfPacket k) := by
        rw [candidate_sum_right, candidate_sum_right]
        apply Finset.sum_congr rfl
        intro i _
        rw [monsterNortonPairHalfPairings_actual, candidate_pairing]
      _ = 1 := monsterNortonPairHalfPacket_norm k
  · rw [monsterNortonPairHalfPacket_norm, monsterNortonPureShort_form]
    simp only [ite_true]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

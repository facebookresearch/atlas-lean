/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole fourth and fifth literal inverse-half states on the second preferred short input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondUpperU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine physical matrix after U on the second A dictionary vector. -/
noncomputable def monsterNortonEvenShortSecondUMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  conwayMatrixAction monsterNortonUFiber.val.2 (trialityPairMatrix monsterNortonEvenShortSecondPair)

/-- This actual transported physical matrix remains symmetric. -/
theorem monsterNortonEvenShortSecondUMatrix_symmetric (i j : Fin 24) :
    monsterNortonEvenShortSecondUMatrix i j = monsterNortonEvenShortSecondUMatrix j i := by
  have hp : (trialityPairMatrix monsterNortonEvenShortSecondPair).transpose =
      trialityPairMatrix monsterNortonEvenShortSecondPair := by
    ext a b
    exact trialityPairMatrix_symmetric _ b a
  have h := congrArg (conwayMatrixAction monsterNortonUFiber.val.2) hp
  rw [conwayMatrixAction_transpose] at h
  exact (congrFun (congrFun h i) j).symm

/-- Actual V fixes this entire pure physical matrix vector. -/
theorem monsterNortonEvenShortSecondUMatrix_V :
    y555NortonV.val (griessConwayDecode (monsterNortonEvenShortSecondUMatrix, (0, 0))) =
      griessConwayDecode (monsterNortonEvenShortSecondUMatrix, (0, 0)) :=
  monsterNortonQ_matrix_fixed y555NortonVQ _ monsterNortonEvenShortSecondUMatrix_symmetric

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The real source preferred octad lift gives the finite complete polar sign.
/-- V's actual phase on the first reached source octad is one. -/
theorem monsterNortonEvenShortSecondUOutputV_phase :
    monsterNortonVShortPhase (monsterNortonEvenShortFirstUOutput 1) = 1 := by
  unfold monsterNortonVShortPhase monsterNortonShortQ
  rw [monsterNortonEvenShortFirstUIntegral_actual]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the opposite source octad's actual polar sign without dropping its central phase.
/-- V's actual phase on the opposite reached source octad is also one. -/
theorem monsterNortonEvenShortSecondUpperUOutputV_phase :
    monsterNortonVShortPhase monsterNortonEvenShortSecondUpperUShortOutput = 1 := by
  unfold monsterNortonVShortPhase monsterNortonShortQ
  rw [monsterNortonEvenShortSecondUpperUShortIntegral_actual]
  decide +kernel

/-- The whole fourth inverse-half packet is its matrix and two original octad short units. -/
noncomputable def monsterNortonEvenShortSecondInverseFourthPacket : GriessSpace :=
  (-1 / 2 : ℝ) • griessConwayDecode (monsterNortonEvenShortSecondUMatrix, (0, 0)) +
    (1 / 2 : ℝ) •
      (monsterNortonPureShort (monsterNortonEvenShortFirstUOutput 1) +
        monsterNortonPureShort monsterNortonEvenShortSecondUpperUShortOutput)

/-- The fourth actual inverse-half U step gives the entire stated vector. -/
theorem monsterNortonEvenShortSecondInverseFourthPacket_actual :
    y555NortonActualU.val monsterNortonEvenShortSecondInverseThirdPacket =
      monsterNortonEvenShortSecondInverseFourthPacket := by
  rw [monsterNortonEvenShortSecondInverseThirdPacket, map_add, map_smul, map_smul,
    monsterNortonU_pair_matrix, monsterNortonEvenShortSecondU_C]
  rfl

/-- The fifth packet retains both actual negative octad signs and the fixed pure matrix. -/
noncomputable def monsterNortonEvenShortSecondInverseFifthPacket : GriessSpace :=
  (-1 / 2 : ℝ) • griessConwayDecode (monsterNortonEvenShortSecondUMatrix, (0, 0)) +
    (-1 / 2 : ℝ) •
      (monsterNortonPureShort (monsterNortonEvenShortFirstUOutput 1) +
        monsterNortonPureShort monsterNortonEvenShortSecondUpperUShortOutput)

/-- Literal V gives the entire fifth inverse-half packet with both checked source phases. -/
theorem monsterNortonEvenShortSecondInverseFifthPacket_actual :
    y555NortonV.val monsterNortonEvenShortSecondInverseFourthPacket =
      monsterNortonEvenShortSecondInverseFifthPacket := by
  rw [monsterNortonEvenShortSecondInverseFourthPacket, map_add, map_smul, map_smul,
    monsterNortonEvenShortSecondUMatrix_V, map_add, monsterNortonV_pure_short,
    monsterNortonV_pure_short, monsterNortonEvenShortSecondUOutputV_phase,
    monsterNortonEvenShortSecondUpperUOutputV_phase]
  simp only [qSign_one, neg_one_smul]
  unfold monsterNortonEvenShortSecondInverseFifthPacket
  module

/-- Five literal inverse-half operators give this complete actual original-coordinate vector. -/
theorem monsterNortonEvenShortSecondInverseFirstFive_actual :
    y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis 1)))))) =
        monsterNortonEvenShortSecondInverseFifthPacket := by
  rw [monsterNortonEvenShortSecondInverseFirstThree_actual,
    monsterNortonEvenShortSecondInverseFourthPacket_actual,
    monsterNortonEvenShortSecondInverseFifthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

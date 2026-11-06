/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full seventh literal line-word state on the second preferred short basis input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every reached second-input short unit lies in the actual pair or octad dictionary family. -/
theorem monsterNortonEvenShortSecondOutput_pair_or_octad (e : Fin 64) :
    monsterNortonEvenShortInverseUKind 1 e = 0 ∨ monsterNortonEvenShortInverseUKind 1 e = 1 := by
  revert e
  decide +kernel

/-- Exact seventh-step physical dictionary image of a reached preferred short unit. -/
noncomputable def monsterNortonEvenShortSecondSeventhTerm (e : Fin 64) : GriessSpace :=
  if monsterNortonEvenShortInverseUKind 1 e = 0 then
    let p := griessPairIndex (monsterNortonEvenShortInverseUPairFirst 1 e)
      (monsterNortonEvenShortInverseUPairSecond 1 e)
      (ne_of_lt (monsterNortonEvenShortInverseUPair_lt 1 e))
    (1 / 2 : ℝ) • trialityABCBasis 0 p +
      (if monsterNortonEvenShortInverseUPairSign 1 e = 0 then (1 / 2 : ℝ) else -1 / 2) •
        trialityABCBasis 2 p
  else
    let a := monsterNortonEvenShortInverseUOctadSlot 1 e
    monsterNortonOctadShortVector
      (monsterNortonOctadIndex (monsterNortonEvenShortInverseUOctadCodes a)
        (monsterNortonEvenShortInverseUOctad_weight a))
      (trialityOctadAction (Pi.single (monsterNortonEvenShortInverseUOctadSign 1 e) 1))

/-- The seventh term is the whole positive triality image, including matrix and short blocks. -/
theorem monsterNortonEvenShortSecondSeventhTerm_actual (e : Fin 64) :
    sExtra (monsterNortonPureShort (monsterNortonEvenShortInverseUOutput 1 e)) =
      monsterNortonEvenShortSecondSeventhTerm e := by
  unfold monsterNortonEvenShortInverseUOutput monsterNortonEvenShortSecondSeventhTerm
  by_cases h0 : monsterNortonEvenShortInverseUKind 1 e = 0
  · simp only [ite_eq_left h0]
    exact monsterNortonPairShort_extra _ _
  · have h1 := (monsterNortonEvenShortSecondOutput_pair_or_octad e).resolve_left h0
    simp only [ite_eq_right h0, ite_eq_left h1]
    unfold monsterNortonPureShort
    rw [← monsterNortonOctadShortVector_single _ _ 1, monsterNortonOctadShortVector_extra]

/-- The entire true seventh packet has all original matrix, pair, and octad summands. -/
noncomputable def monsterNortonEvenShortSecondSeventhPacket : GriessSpace :=
  ∑ e : Fin 64, monsterNortonEvenShortSecondSixthCoefficient e •
    monsterNortonEvenShortSecondSeventhTerm e

/-- Actual positive triality transports the complete sixth vector to the stated seventh vector. -/
theorem monsterNortonEvenShortSecondSeventhPacket_actual :
    sExtra monsterNortonEvenShortSecondSixthPacket =
      monsterNortonEvenShortSecondSeventhPacket := by
  rw [monsterNortonEvenShortSecondSixthPacket, map_sum]
  simp only [map_smul, monsterNortonEvenShortSecondSeventhTerm_actual]
  rfl

/-- Seven literal operators give the complete original-coordinate second-basis image. -/
theorem monsterNortonEvenShortSecondFirstSeven_actual :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 1)))))))) =
      qSign (monsterNortonEvenShortInitialVPhase 1) •
        monsterNortonEvenShortSecondSeventhPacket := by
  rw [monsterNortonEvenShortSecondFirstSix_actual, map_smul,
    monsterNortonEvenShortSecondSeventhPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

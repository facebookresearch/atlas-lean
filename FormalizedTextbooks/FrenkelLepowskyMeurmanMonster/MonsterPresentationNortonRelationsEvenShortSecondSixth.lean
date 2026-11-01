/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete fifth and sixth literal line-word states on the second preferred short basis input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUQ1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFourth

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete fifth packet coefficient, including the actual inverse-U central phase. -/
noncomputable def monsterNortonEvenShortSecondFifthCoefficient (e : Fin 64) : ℝ :=
  (((monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign 1) : ℝ) / 8) *
    qSign (monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput 1 e))) *
      qSign (monsterNortonEvenShortInverseUPhase 1 e)

/-- Sixty-four signed original short units form the entire fifth second-basis packet. -/
noncomputable def monsterNortonEvenShortSecondFifthPacket : GriessSpace :=
  ∑ e : Fin 64, monsterNortonEvenShortSecondFifthCoefficient e •
    monsterNortonPureShort (monsterNortonEvenShortInverseUOutput 1 e)

/-- Actual inverse U takes the complete fourth second-basis packet to the stated fifth packet. -/
theorem monsterNortonEvenShortSecondFifthPacket_actual :
    (y555NortonActualU⁻¹).val (monsterNortonEvenShortFourthPacket 1) =
      monsterNortonEvenShortSecondFifthPacket := by
  have h : ¬monsterNortonEvenShortFirstUIsOdd (1 : Fin 23) = true := by decide +kernel
  unfold monsterNortonEvenShortFourthPacket
  rw [ite_eq_right h]
  change (y555NortonActualU⁻¹).val (∑ e : Fin 64,
    (((monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign 1) : ℝ) /
      8) * qSign (monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput 1 e))) •
        monsterNortonPureShort (monsterNortonEvenShortInverseUInput 1 e)) = _
  rw [map_sum]
  simp only [map_smul, monsterNortonEvenShortInverseUQ1_unit, smul_smul]
  rfl

/-- The sixth coefficient keeps the actual next V sign of each reached preferred output. -/
noncomputable def monsterNortonEvenShortSecondSixthCoefficient (e : Fin 64) : ℝ :=
  monsterNortonEvenShortSecondFifthCoefficient e *
    qSign (monsterNortonVShortPhase (monsterNortonEvenShortInverseUOutput 1 e))

/-- The whole signed original-coordinate packet following the sixth literal V. -/
noncomputable def monsterNortonEvenShortSecondSixthPacket : GriessSpace :=
  ∑ e : Fin 64, monsterNortonEvenShortSecondSixthCoefficient e •
    monsterNortonPureShort (monsterNortonEvenShortInverseUOutput 1 e)

/-- Actual V gives the complete stated sixth packet. -/
theorem monsterNortonEvenShortSecondSixthPacket_actual :
    y555NortonV.val monsterNortonEvenShortSecondFifthPacket =
      monsterNortonEvenShortSecondSixthPacket := by
  rw [monsterNortonEvenShortSecondFifthPacket, map_sum]
  simp only [map_smul, monsterNortonV_pure_short, smul_smul]
  rfl

/-- Six literal operators give the entire true vector on the second preferred short basis input. -/
theorem monsterNortonEvenShortSecondFirstSix_actual :
    y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 1))))))) =
      qSign (monsterNortonEvenShortInitialVPhase 1) • monsterNortonEvenShortSecondSixthPacket := by
  rw [monsterNortonEvenShortFirstFour_actual, map_smul,
    monsterNortonEvenShortSecondFifthPacket_actual, map_smul,
    monsterNortonEvenShortSecondSixthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

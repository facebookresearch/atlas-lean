/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete seventh literal distance-two packets for the eight middle preferred basis slots. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairOctadTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02Sixth

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original preferred basis slot attached to one of the eight middle packet rows. -/
def monsterNortonLine02MiddleBasis (a : Fin 8) : Fin 23 :=
  Fin.natAdd 2 (Fin.castAdd 13 a)

/-- The full explicit pair-matrix or octad Fourier vector after the seventh triality step. -/
noncomputable def monsterNortonLine02MiddleExtraOutput (a : Fin 8) (e : Fin 64) : GriessSpace :=
  if monsterNortonLine02MiddleOutputKind a e = 0 then
    let p := griessPairIndex (monsterNortonLine02MiddlePairFirst a e)
      (monsterNortonLine02MiddlePairSecond a e)
      (ne_of_lt (monsterNortonLine02MiddlePair_lt a e))
    (1 / 2 : ℝ) • trialityABCBasis 0 p +
      (if monsterNortonLine02MiddlePairSign a e = 0 then (1 / 2 : ℝ) else -1 / 2) •
        trialityABCBasis 2 p
  else
    let d := monsterNortonOctadIndex
      (monsterNortonLine02MiddleOctadCode (monsterNortonLine02MiddleOctadChoice a e))
      (monsterNortonLine02MiddleOctad_weight (monsterNortonLine02MiddleOctadChoice a e))
    ∑ f : Fin 64,
      monsterNortonOctadTrialityCoefficient f (monsterNortonLine02MiddleOctadSign a e) •
        monsterNortonPureShort (Sum.inr (Sum.inl (d, f)))

/-- Every stored seventh output is the whole actual forward triality image. -/
theorem monsterNortonLine02MiddleExtraOutput_actual (a : Fin 8) (e : Fin 64) :
    sExtra (monsterNortonPureShort (monsterNortonLine02MiddleOutput a e)) =
      monsterNortonLine02MiddleExtraOutput a e := by
  unfold monsterNortonLine02MiddleOutput monsterNortonLine02MiddleExtraOutput
  by_cases h : monsterNortonLine02MiddleOutputKind a e = 0
  · simp only [h, ite_true]
    exact monsterNortonPairShort_extra _ _
  · simp only [h, ite_false]
    exact monsterNortonOctadPureShort_extra _ _

/-- The fourth packet coefficient before the inverse-squared middle short action. -/
noncomputable def monsterNortonLine02MiddleFourthCoefficient (a : Fin 8) (e : Fin 64) : ℝ :=
  ((monsterNortonOctadInverseCoefficient e
    (monsterNortonLine02FirstUOctadSign (monsterNortonLine02MiddleBasis a)) : ℝ) / 8) *
      qSign (monsterNortonVShortPhase (monsterNortonLine02MiddleInput a e))

/-- Its full phase-complete coefficient after inverse-squared U and literal V. -/
noncomputable def monsterNortonLine02MiddleForwardCoefficient (a : Fin 8) (e : Fin 64) : ℝ :=
  monsterNortonLine02MiddleFourthCoefficient a e * qSign (monsterNortonLine02MiddlePhase a e) *
    qSign (monsterNortonVShortPhase (monsterNortonLine02MiddleOutput a e))

/-- The complete finite matrix and short packet after all seven literal forward steps. -/
noncomputable def monsterNortonLine02MiddleForwardPacket (a : Fin 8) : GriessSpace :=
  ∑ e : Fin 64, monsterNortonLine02MiddleForwardCoefficient a e •
    monsterNortonLine02MiddleExtraOutput a e

private theorem four_packet (a : Fin 8) :
    monsterNortonLine02FourthPacket (monsterNortonLine02MiddleBasis a) =
      ∑ e : Fin 64, monsterNortonLine02MiddleFourthCoefficient a e •
        monsterNortonPureShort (monsterNortonLine02MiddleInput a e) := by
  have h : monsterNortonLine02FirstUIsOdd (monsterNortonLine02MiddleBasis a) = false := by
    revert a
    decide +kernel
  unfold monsterNortonLine02FourthPacket
  rw [h]
  rfl

private theorem final_three (a : Fin 8) (e : Fin 64) (c : ℝ) :
    sExtra (y555NortonV.val (((y555NortonActualU ^ 2)⁻¹).val
      (c • monsterNortonPureShort (monsterNortonLine02MiddleInput a e)))) =
      (c * qSign (monsterNortonLine02MiddlePhase a e) *
        qSign (monsterNortonVShortPhase (monsterNortonLine02MiddleOutput a e))) •
          monsterNortonLine02MiddleExtraOutput a e := by
  simp only [map_smul, monsterNortonLine02MiddleShort_inverse,
    monsterNortonV_pure_short, monsterNortonLine02MiddleExtraOutput_actual, smul_smul]

/-- The whole actual first seven states agree with the full original-coordinate forward packet. -/
theorem monsterNortonLine02MiddleForwardPacket_actual (a : Fin 8) :
    sExtra (y555NortonV.val (((y555NortonActualU ^ 2)⁻¹).val (y555NortonV.val (sExtra.symm
      ((y555NortonActualU ^ 2).val (y555NortonV.val (monsterNortonPureShort
        (monsterNortonEvenShortBasis (monsterNortonLine02MiddleBasis a))))))))) =
      qSign (monsterNortonLine02FirstThreePhase (monsterNortonLine02MiddleBasis a)) •
        monsterNortonLine02MiddleForwardPacket a := by
  rw [monsterNortonLine02FirstFour_actual, map_smul, map_smul, map_smul, four_packet]
  congr 1
  simp only [map_sum, final_three, monsterNortonLine02MiddleForwardPacket,
    monsterNortonLine02MiddleForwardCoefficient]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual forward-half expansion with every source phase retained. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneForwardCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ReturnFromPackets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput 21 e) =
      monsterNortonCodeTwentyOneVSourcePhase (monsterNortonEvenShortInverseUInputQ 21 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeTwentyOneVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonShortQSource_eq,
    monsterNortonEvenShortInverseUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUOutput 21 e) =
      monsterNortonCodeTwentyOneVSourcePhase (monsterNortonCodeTwentyOneForwardOutputQ e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeTwentyOneVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonCodeTwentyOneForwardOutputQ_actual]

/-- Every complete actual sixth coefficient equals its full signed integer cache divided by eight.
-/
theorem monsterNortonCodeTwentyOneForwardCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonEvenShortInitialVPhase 21) *
      monsterNortonEvenShortSixthCoefficient 21 e =
        (monsterNortonCodeTwentyOneForwardCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeTwentyOneForwardCoefficient_cache]
  unfold monsterNortonEvenShortSixthCoefficient monsterNortonEvenShortFifthCoefficient
    monsterNortonCodeTwentyOneForwardCoefficient
  rw [input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete sixty-four-term actual seventh packet, including every reached constituent. -/
noncomputable def monsterNortonCodeTwentyOneForwardActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeTwentyOneForwardCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonEvenShortInverseUOutput 21 e)

/-- Seven literal original word operators give this whole phase-complete packet. -/
theorem monsterNortonCodeTwentyOneForwardActualPacket_actual :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 21)))))))) =
      monsterNortonCodeTwentyOneForwardActualPacket := by
  have h := monsterNortonEvenShortFirstSeven_actual 21
  unfold monsterNortonEvenShortSeventhPacket at h
  simp only [show monsterNortonEvenShortFirstUIsOdd 21 = false from rfl,
    Bool.false_eq_true, ite_false] at h
  rw [Finset.smul_sum] at h
  simp_rw [smul_smul, monsterNortonCodeTwentyOneForwardCoefficient_actual] at h
  exact h

/-- The complete actual seventh packet has original Griess squared norm one. -/
theorem monsterNortonCodeTwentyOneForwardActualPacket_norm :
    griessForm monsterNortonCodeTwentyOneForwardActualPacket
      monsterNortonCodeTwentyOneForwardActualPacket = 1 := by
  let x := monsterNortonPureShort (monsterNortonEvenShortBasis 21)
  have h := generated_group_preserves_griessForm monsterNortonSecondForwardHalf x x
  change griessForm
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x)))))))
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x))))))) = griessForm x x at h
  dsimp only [x] at h
  rw [monsterNortonCodeTwentyOneForwardActualPacket_actual, monsterNortonPureShort_form] at h
  simpa only [ite_true] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

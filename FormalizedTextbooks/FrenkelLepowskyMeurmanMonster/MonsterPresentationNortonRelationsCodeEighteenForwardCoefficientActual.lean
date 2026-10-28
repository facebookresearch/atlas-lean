/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual forward-half expansion with every source phase retained. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenForwardCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ReturnFromPackets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput 18 e) =
      monsterNortonCodeEighteenVSourcePhase (monsterNortonEvenShortInverseUInputQ 18 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeEighteenVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonShortQSource_eq,
    monsterNortonEvenShortInverseUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUOutput 18 e) =
      monsterNortonCodeEighteenVSourcePhase (monsterNortonCodeEighteenForwardOutputQ e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeEighteenVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonCodeEighteenForwardOutputQ_actual]

/-- Every complete actual sixth coefficient equals its full signed integer cache divided by eight.
-/
theorem monsterNortonCodeEighteenForwardCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonEvenShortInitialVPhase 18) *
      monsterNortonEvenShortSixthCoefficient 18 e =
        (monsterNortonCodeEighteenForwardCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeEighteenForwardCoefficient_cache]
  unfold monsterNortonEvenShortSixthCoefficient monsterNortonEvenShortFifthCoefficient
    monsterNortonCodeEighteenForwardCoefficient
  rw [input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete sixty-four-term actual seventh packet, including every reached constituent. -/
noncomputable def monsterNortonCodeEighteenForwardActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeEighteenForwardCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonEvenShortInverseUOutput 18 e)

/-- Seven literal original word operators give this whole phase-complete packet. -/
theorem monsterNortonCodeEighteenForwardActualPacket_actual :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 18)))))))) =
      monsterNortonCodeEighteenForwardActualPacket := by
  have h := monsterNortonEvenShortFirstSeven_actual 18
  unfold monsterNortonEvenShortSeventhPacket at h
  simp only [show monsterNortonEvenShortFirstUIsOdd 18 = false from rfl,
    Bool.false_eq_true, ite_false] at h
  rw [Finset.smul_sum] at h
  simp_rw [smul_smul, monsterNortonCodeEighteenForwardCoefficient_actual] at h
  exact h

/-- The complete actual seventh packet has original Griess squared norm one. -/
theorem monsterNortonCodeEighteenForwardActualPacket_norm :
    griessForm monsterNortonCodeEighteenForwardActualPacket
      monsterNortonCodeEighteenForwardActualPacket = 1 := by
  let x := monsterNortonPureShort (monsterNortonEvenShortBasis 18)
  have h := generated_group_preserves_griessForm monsterNortonSecondForwardHalf x x
  change griessForm
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x)))))))
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x))))))) = griessForm x x at h
  dsimp only [x] at h
  rw [monsterNortonCodeEighteenForwardActualPacket_actual, monsterNortonPureShort_form] at h
  simpa only [ite_true] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

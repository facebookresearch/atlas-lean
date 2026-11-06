/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual forward-half expansion with every source phase retained. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenForwardCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ReturnFromPackets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput 19 e) =
      monsterNortonCodeNineteenVSourcePhase (monsterNortonEvenShortInverseUInputQ 19 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeNineteenVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonShortQSource_eq,
    monsterNortonEvenShortInverseUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUOutput 19 e) =
      monsterNortonCodeNineteenVSourcePhase (monsterNortonCodeNineteenForwardOutputQ e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeNineteenVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonCodeNineteenForwardOutputQ_actual]

/-- Every complete actual sixth coefficient equals its full signed integer cache divided by eight.
-/
theorem monsterNortonCodeNineteenForwardCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonEvenShortInitialVPhase 19) *
      monsterNortonEvenShortSixthCoefficient 19 e =
        (monsterNortonCodeNineteenForwardCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeNineteenForwardCoefficient_cache]
  unfold monsterNortonEvenShortSixthCoefficient monsterNortonEvenShortFifthCoefficient
    monsterNortonCodeNineteenForwardCoefficient
  rw [input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete sixty-four-term actual seventh packet, including every reached constituent. -/
noncomputable def monsterNortonCodeNineteenForwardActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeNineteenForwardCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonEvenShortInverseUOutput 19 e)

/-- Seven literal original word operators give this whole phase-complete packet. -/
theorem monsterNortonCodeNineteenForwardActualPacket_actual :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 19)))))))) =
      monsterNortonCodeNineteenForwardActualPacket := by
  have h := monsterNortonEvenShortFirstSeven_actual 19
  unfold monsterNortonEvenShortSeventhPacket at h
  simp only [show monsterNortonEvenShortFirstUIsOdd 19 = false from rfl,
    Bool.false_eq_true, ite_false] at h
  rw [Finset.smul_sum] at h
  simp_rw [smul_smul, monsterNortonCodeNineteenForwardCoefficient_actual] at h
  exact h

/-- The complete actual seventh packet has original Griess squared norm one. -/
theorem monsterNortonCodeNineteenForwardActualPacket_norm :
    griessForm monsterNortonCodeNineteenForwardActualPacket
      monsterNortonCodeNineteenForwardActualPacket = 1 := by
  let x := monsterNortonPureShort (monsterNortonEvenShortBasis 19)
  have h := generated_group_preserves_griessForm monsterNortonSecondForwardHalf x x
  change griessForm
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x)))))))
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x))))))) = griessForm x x at h
  dsimp only [x] at h
  rw [monsterNortonCodeNineteenForwardActualPacket_actual, monsterNortonPureShort_form] at h
  simpa only [ite_true] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

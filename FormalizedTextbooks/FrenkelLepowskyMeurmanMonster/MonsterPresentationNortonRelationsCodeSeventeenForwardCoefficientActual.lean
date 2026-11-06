/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual forward-half expansion with every source phase retained. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenForwardCoefficientCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ReturnFromPackets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem input_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput 17 e) =
      monsterNortonCodeSeventeenVSourcePhase (monsterNortonEvenShortInverseUInputQ 17 e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeSeventeenVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonShortQSource_eq,
    monsterNortonEvenShortInverseUInputQ_actual]

private theorem output_phase (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUOutput 17 e) =
      monsterNortonCodeSeventeenVSourcePhase (monsterNortonCodeSeventeenForwardOutputQ e) := by
  unfold monsterNortonVShortPhase monsterNortonCodeSeventeenVSourcePhase
  rw [← monsterNortonShortQSource_eq, monsterNortonCodeSeventeenForwardOutputQ_actual]

/-- Every complete actual sixth coefficient equals its full signed integer cache divided by eight.
-/
theorem monsterNortonCodeSeventeenForwardCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonEvenShortInitialVPhase 17) *
      monsterNortonEvenShortSixthCoefficient 17 e =
        (monsterNortonCodeSeventeenForwardCoefficientCache e : ℝ) / 8 := by
  rw [← monsterNortonCodeSeventeenForwardCoefficient_cache]
  unfold monsterNortonEvenShortSixthCoefficient monsterNortonEvenShortFifthCoefficient
    monsterNortonCodeSeventeenForwardCoefficient
  rw [input_phase, output_phase]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- The complete sixty-four-term actual seventh packet, including every reached constituent. -/
noncomputable def monsterNortonCodeSeventeenForwardActualPacket : GriessSpace :=
  ∑ e : Fin 64, ((monsterNortonCodeSeventeenForwardCoefficientCache e : ℝ) / 8) •
    monsterNortonShortExtraPacket (monsterNortonEvenShortInverseUOutput 17 e)

/-- Seven literal original word operators give this whole phase-complete packet. -/
theorem monsterNortonCodeSeventeenForwardActualPacket_actual :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 17)))))))) =
      monsterNortonCodeSeventeenForwardActualPacket := by
  have h := monsterNortonEvenShortFirstSeven_actual 17
  unfold monsterNortonEvenShortSeventhPacket at h
  simp only [show monsterNortonEvenShortFirstUIsOdd 17 = false from rfl,
    Bool.false_eq_true, ite_false] at h
  rw [Finset.smul_sum] at h
  simp_rw [smul_smul, monsterNortonCodeSeventeenForwardCoefficient_actual] at h
  exact h

/-- The complete actual seventh packet has original Griess squared norm one. -/
theorem monsterNortonCodeSeventeenForwardActualPacket_norm :
    griessForm monsterNortonCodeSeventeenForwardActualPacket
      monsterNortonCodeSeventeenForwardActualPacket = 1 := by
  let x := monsterNortonPureShort (monsterNortonEvenShortBasis 17)
  have h := generated_group_preserves_griessForm monsterNortonSecondForwardHalf x x
  change griessForm
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x)))))))
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x))))))) = griessForm x x at h
  dsimp only [x] at h
  rw [monsterNortonCodeSeventeenForwardActualPacket_actual, monsterNortonPureShort_form] at h
  simpa only [ite_true] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

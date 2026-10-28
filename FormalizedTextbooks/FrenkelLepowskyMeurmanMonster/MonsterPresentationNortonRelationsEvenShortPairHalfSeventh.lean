/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full seventh literal line-word state on the second preferred short basis input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every reached second-input short unit lies in the actual pair or octad dictionary family. -/
theorem monsterNortonEvenShortPairHalfOutput_pair_or_octad (k : Fin 12) (e : Fin 64) :
    monsterNortonEvenShortInverseUKind (monsterNortonPairHalfBasisIndex k) e = 0 ∨
      monsterNortonEvenShortInverseUKind (monsterNortonPairHalfBasisIndex k) e = 1 := by
  revert k e
  decide +kernel

/-- Exact seventh-step physical dictionary image of a reached preferred short unit. -/
noncomputable def monsterNortonEvenShortPairHalfSeventhTerm
    (k : Fin 12) (e : Fin 64) : GriessSpace :=
  if monsterNortonEvenShortInverseUKind (monsterNortonPairHalfBasisIndex k) e = 0 then
    let p := griessPairIndex
      (monsterNortonEvenShortInverseUPairFirst (monsterNortonPairHalfBasisIndex k) e)
      (monsterNortonEvenShortInverseUPairSecond (monsterNortonPairHalfBasisIndex k) e)
      (ne_of_lt (monsterNortonEvenShortInverseUPair_lt (monsterNortonPairHalfBasisIndex k) e))
    (1 / 2 : ℝ) • trialityABCBasis 0 p +
      (if monsterNortonEvenShortInverseUPairSign (monsterNortonPairHalfBasisIndex k) e = 0 then
        (1 / 2 : ℝ) else -1 / 2) •
        trialityABCBasis 2 p
  else
    let a := monsterNortonEvenShortInverseUOctadSlot (monsterNortonPairHalfBasisIndex k) e
    monsterNortonOctadShortVector
      (monsterNortonOctadIndex (monsterNortonEvenShortInverseUOctadCodes a)
        (monsterNortonEvenShortInverseUOctad_weight a))
      (trialityOctadAction (Pi.single
        (monsterNortonEvenShortInverseUOctadSign (monsterNortonPairHalfBasisIndex k) e) 1))

/-- The seventh term is the whole positive triality image, including matrix and short blocks. -/
theorem monsterNortonEvenShortPairHalfSeventhTerm_actual (k : Fin 12) (e : Fin 64) :
    sExtra (monsterNortonPureShort
      (monsterNortonEvenShortInverseUOutput (monsterNortonPairHalfBasisIndex k) e)) =
      (monsterNortonEvenShortPairHalfSeventhTerm k) e := by
  unfold monsterNortonEvenShortInverseUOutput monsterNortonEvenShortPairHalfSeventhTerm
  by_cases h0 : monsterNortonEvenShortInverseUKind (monsterNortonPairHalfBasisIndex k) e = 0
  · simp only [ite_eq_left h0]
    exact monsterNortonPairShort_extra _ _
  · have h1 := ((monsterNortonEvenShortPairHalfOutput_pair_or_octad k) e).resolve_left h0
    simp only [ite_eq_right h0, ite_eq_left h1]
    unfold monsterNortonPureShort
    rw [← monsterNortonOctadShortVector_single _ _ 1, monsterNortonOctadShortVector_extra]

/-- No first-U odd branch occurs at these twelve original basis entries. -/
theorem monsterNortonPairHalf_firstU_even (k : Fin 12) :
    monsterNortonEvenShortFirstUIsOdd (monsterNortonPairHalfBasisIndex k) = false := by
  revert k
  decide +kernel

/-- The entire actual seventh packet equals the sum of its full pair and octad terms. -/
theorem monsterNortonPairHalf_seventh_sum (k : Fin 12) :
    monsterNortonEvenShortSeventhPacket (monsterNortonPairHalfBasisIndex k) =
      ∑ e : Fin 64,
        monsterNortonEvenShortSixthCoefficient (monsterNortonPairHalfBasisIndex k) e •
          monsterNortonEvenShortPairHalfSeventhTerm k e := by
  unfold monsterNortonEvenShortSeventhPacket
  rw [monsterNortonPairHalf_firstU_even]
  simp only [Bool.false_eq_true, ite_false]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  rw [← monsterNortonShortExtraPacket_actual,
    monsterNortonEvenShortPairHalfSeventhTerm_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

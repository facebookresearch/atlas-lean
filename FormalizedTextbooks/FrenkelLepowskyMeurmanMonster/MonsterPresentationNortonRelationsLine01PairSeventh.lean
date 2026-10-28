/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact actual seventh state of the first pair-short line-square test. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original matrix/pair or octad Fourier image of each reached short coordinate. -/
noncomputable def monsterNortonLine01PairSeventhTerm (e : Fin 64) : GriessSpace :=
  if monsterNortonLine01PairInverseIsPair e then
    let p := griessPairIndex (monsterNortonLine01PairInversePairFirst e)
      (monsterNortonLine01PairInversePairSecond e)
        (ne_of_lt (monsterNortonLine01PairInversePair_increasing e))
    (1 / 2 : ℝ) • trialityABCBasis 0 p +
      (if monsterNortonLine01PairInversePairSign e = 0 then (1 / 2 : ℝ) else -1 / 2) •
        trialityABCBasis 2 p
  else
    monsterNortonOctadShortVector
      (monsterNortonOctadIndex
        (monsterNortonLine01PairInverseOctadCodes (monsterNortonLine01PairInverseOctadSlot e))
        (monsterNortonLine01PairInverseOctad_weight (monsterNortonLine01PairInverseOctadSlot e)))
      (trialityOctadAction (Pi.single (monsterNortonLine01PairInverseOctadSign e) 1))

/-- Every displayed seventh-state term is the full actual positive-triality image. -/
theorem monsterNortonLine01PairSeventhTerm_actual (e : Fin 64) :
    sExtra (monsterNortonPureShort (monsterNortonLine01PairInverseShortOutput e)) =
      monsterNortonLine01PairSeventhTerm e := by
  unfold monsterNortonLine01PairInverseShortOutput monsterNortonLine01PairSeventhTerm
  by_cases h : monsterNortonLine01PairInverseIsPair e = true
  · simp only [ite_eq_left h]
    exact monsterNortonPairShort_extra _ _
  · simp only [ite_eq_right h]
    have hs := monsterNortonOctadShortVector_single
      (monsterNortonOctadIndex
        (monsterNortonLine01PairInverseOctadCodes (monsterNortonLine01PairInverseOctadSlot e))
        (monsterNortonLine01PairInverseOctad_weight (monsterNortonLine01PairInverseOctadSlot e)))
      (monsterNortonLine01PairInverseOctadSign e) 1
    rw [monsterNortonPureShort, ← hs, monsterNortonOctadShortVector_extra]

/-- The entire actual seventh state as a finite sum of original matrix/pair and octad blocks. -/
noncomputable def monsterNortonLine01PairAfterSeventh : GriessSpace :=
  ∑ e, (((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8) *
    qSign (monsterNortonLine01PairOctadVPhase e) *
      qSign (monsterNortonLine01PairInverseVPhase e)) • monsterNortonLine01PairSeventhTerm e

/-- Seven literal source operators give this full phase-correct Conway-coordinate expansion. -/
theorem monsterNortonLine01PairSeventh_actual :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val
      (y555NortonV.val monsterNortonLine01PairAfterVUExtraInverse))) =
        monsterNortonLine01PairAfterSeventh := by
  rw [monsterNortonLine01PairSixth_actual, monsterNortonLine01PairAfterInverseUV, map_sum]
  simp only [map_smul, monsterNortonLine01PairSeventhTerm_actual]
  rfl

/-- The first seven literal operators on the original pair unit match the complete expansion. -/
theorem monsterNortonLine01PairSeventh_literal :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val
      (y555NortonV.val (sExtra.symm (y555NortonActualU.val
        (y555NortonV.val (monsterNortonPureShort monsterNortonLine01PairShortInput))))))) =
          monsterNortonLine01PairAfterSeventh := by
  rw [monsterNortonLine01PairExtraInverse_actual]
  exact monsterNortonLine01PairSeventh_actual

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

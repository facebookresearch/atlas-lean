/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete fifth distance-two states in the original Conway coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02Fourth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoTensorColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoShortCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A fifth packet is a full sixteen-term spin numerator or sixty-four signed short units. -/
noncomputable def monsterNortonLine02FifthPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonLine02FirstUIsOdd k then
    monsterNortonTensorRankOne (((monsterNortonUFiber⁻¹) ^ 2).val.2.val
      (Pi.single (monsterNortonLine02FirstUOddPosition k) 1))
      ((qSign (golayMaskWeight
        (golayEncodedMask (monsterNortonLine02FirstUOddCode k).val) / 4 : ℕ) /
          Real.sqrt 2) • ((1 / 4 : ℝ) • nortonUIntegerEmbed
            (monsterNortonUTwoCompactInverseNumerator (nortonUIntegerQ y555NortonVQ
              (monsterNortonSourceZInteger (monsterNortonLine02FirstUOddCode k))))))
  else
    let d := monsterNortonOctadIndex (monsterNortonLine02FirstUOctadCodes k)
      (monsterNortonLine02FirstUOctad_weight k)
    ∑ e : Fin 64,
      (((monsterNortonOctadInverseCoefficient e (monsterNortonLine02FirstUOctadSign k) : ℝ) /
        8) * qSign (monsterNortonVShortPhase (Sum.inr (Sum.inl (d, e)))) *
          qSign (monsterNortonUTwoInverseShortPhase (Sum.inr (Sum.inl (d, e))))) •
            monsterNortonPureShort
              (monsterNortonUTwoInverseShortOutput (Sum.inr (Sum.inl (d, e))))

/-- The actual inverse-squared Norton element transports the whole fourth packet. -/
theorem monsterNortonLine02FifthPacket_actual (k : Fin 23) :
    ((y555NortonActualU ^ 2)⁻¹).val (monsterNortonLine02FourthPacket k) =
      monsterNortonLine02FifthPacket k := by
  unfold monsterNortonLine02FourthPacket monsterNortonLine02FifthPacket
  by_cases h : monsterNortonLine02FirstUIsOdd k = true
  · simp only [ite_eq_left h]
    exact monsterNortonUTwoInverse_source_ZQ_column y555NortonVQ _ _
  · simp only [ite_eq_right h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_smul, monsterNortonUTwoInverse_pure_short, smul_smul]

/-- Every original preferred short unit has the stated complete fifth literal state. -/
theorem monsterNortonLine02FirstFive_actual (k : Fin 23) :
    ((y555NortonActualU ^ 2)⁻¹).val (y555NortonV.val (sExtra.symm
      ((y555NortonActualU ^ 2).val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis k)))))) =
      qSign (monsterNortonLine02FirstThreePhase k) • monsterNortonLine02FifthPacket k := by
  rw [monsterNortonLine02FirstFour_actual, map_smul, monsterNortonLine02FifthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

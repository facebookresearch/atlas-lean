/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete fourth literal distance-two states on all original preferred short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02Third
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFourth

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The fourth packet contains sixty-four short units or two translated spin deltas. -/
noncomputable def monsterNortonLine02FourthPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonLine02FirstUIsOdd k then
    monsterNortonTensorLift (conwaySpinColumn
      (monsterNortonSourceZQSpinImage y555NortonVQ (monsterNortonLine02FirstUOddCode k))
      (monsterNortonLine02FirstUOddPosition k))
  else
    let d := monsterNortonOctadIndex (monsterNortonLine02FirstUOctadCodes k)
      (monsterNortonLine02FirstUOctad_weight k)
    ∑ e : Fin 64,
      (((monsterNortonOctadInverseCoefficient e (monsterNortonLine02FirstUOctadSign k) : ℝ) /
        8) * qSign (monsterNortonVShortPhase (Sum.inr (Sum.inl (d, e))))) •
          monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))

/-- Literal V takes the whole third packet to the stated fourth packet. -/
theorem monsterNortonLine02FourthPacket_actual (k : Fin 23) :
    y555NortonV.val (monsterNortonLine02ThirdPacket k) =
      monsterNortonLine02FourthPacket k := by
  unfold monsterNortonLine02ThirdPacket monsterNortonLine02FourthPacket
  by_cases h : monsterNortonLine02FirstUIsOdd k = true
  · simp only [ite_eq_left h]
    exact monsterNortonQ_source_Z_explicit y555NortonVQ _ _
  · simp only [ite_eq_right h]
    exact monsterNortonV_octad_packet _ _

/-- Complete original-coordinate state after four literal V, U, inverse-triality, V steps. -/
theorem monsterNortonLine02FirstFour_actual (k : Fin 23) :
    y555NortonV.val (sExtra.symm ((y555NortonActualU ^ 2).val (y555NortonV.val
      (monsterNortonPureShort (monsterNortonEvenShortBasis k))))) =
      qSign (monsterNortonLine02FirstThreePhase k) • monsterNortonLine02FourthPacket k := by
  rw [monsterNortonLine02FirstThree_actual, map_smul, monsterNortonLine02FourthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

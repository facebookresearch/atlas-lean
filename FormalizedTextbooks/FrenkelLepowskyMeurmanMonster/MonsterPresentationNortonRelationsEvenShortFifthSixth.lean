/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete fifth and sixth literal line-word states on every preferred short basis input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortOddSixth

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Full actual scalar of each reached short unit after inverse U. -/
noncomputable def monsterNortonEvenShortFifthCoefficient (k : Fin 23) (e : Fin 64) : ℝ :=
  (((monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign k) : ℝ) / 8) *
    qSign (monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput k e))) *
      qSign (monsterNortonEvenShortInverseUPhase k e)

/-- Complete fifth packet, with the genuine odd tensor branch or sixty-four signed short units. -/
noncomputable def monsterNortonEvenShortFifthPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonEvenShortFirstUIsOdd k then monsterNortonEvenShortOddFifthPacket k else
    ∑ e : Fin 64, monsterNortonEvenShortFifthCoefficient k e •
      monsterNortonPureShort (monsterNortonEvenShortInverseUOutput k e)

/-- Actual inverse U takes the whole fourth packet to its phase-complete fifth packet. -/
theorem monsterNortonEvenShortFifthPacket_actual (k : Fin 23) :
    (y555NortonActualU⁻¹).val (monsterNortonEvenShortFourthPacket k) =
      monsterNortonEvenShortFifthPacket k := by
  unfold monsterNortonEvenShortFifthPacket
  by_cases hk : monsterNortonEvenShortFirstUIsOdd k = true
  · rw [ite_eq_left hk]
    exact monsterNortonEvenShortOddFifthPacket_actual k hk
  · rw [ite_eq_right hk]
    unfold monsterNortonEvenShortFourthPacket
    rw [ite_eq_right hk]
    change (y555NortonActualU⁻¹).val (∑ e : Fin 64,
      (((monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign k) : ℝ) /
        8) * qSign (monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput k e))) •
          monsterNortonPureShort (monsterNortonEvenShortInverseUInput k e)) = _
    rw [map_sum]
    simp only [map_smul, monsterNortonEvenShortInverseU_unit, smul_smul]
    rfl

/-- The next V scalar retains the actual central polar phase of every reached preferred output. -/
noncomputable def monsterNortonEvenShortSixthCoefficient (k : Fin 23) (e : Fin 64) : ℝ :=
  monsterNortonEvenShortFifthCoefficient k e *
    qSign (monsterNortonVShortPhase (monsterNortonEvenShortInverseUOutput k e))

/-- The entire sixth physical packet has its true tensor or signed-short branch. -/
noncomputable def monsterNortonEvenShortSixthPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonEvenShortFirstUIsOdd k then monsterNortonEvenShortOddSixthPacket k else
    ∑ e : Fin 64, monsterNortonEvenShortSixthCoefficient k e •
      monsterNortonPureShort (monsterNortonEvenShortInverseUOutput k e)

/-- Actual V takes each entire fifth vector to its complete stated sixth vector. -/
theorem monsterNortonEvenShortSixthPacket_actual (k : Fin 23) :
    y555NortonV.val (monsterNortonEvenShortFifthPacket k) =
      monsterNortonEvenShortSixthPacket k := by
  unfold monsterNortonEvenShortFifthPacket monsterNortonEvenShortSixthPacket
  by_cases hk : monsterNortonEvenShortFirstUIsOdd k = true
  · simp only [ite_eq_left hk]
    exact monsterNortonEvenShortOddSixthPacket_actual k
  · simp only [ite_eq_right hk]
    rw [map_sum]
    simp only [map_smul, monsterNortonV_pure_short, smul_smul]
    rfl

/-- Six literal operators have the complete original-coordinate image on all twenty-three inputs. -/
theorem monsterNortonEvenShortFirstSix_actual (k : Fin 23) :
    y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis k))))))) =
      qSign (monsterNortonEvenShortInitialVPhase k) • monsterNortonEvenShortSixthPacket k := by
  rw [monsterNortonEvenShortFirstFour_actual, map_smul, monsterNortonEvenShortFifthPacket_actual,
    map_smul, monsterNortonEvenShortSixthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

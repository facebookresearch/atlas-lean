/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual first three distance-two line-word states
   on all original preferred short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02FirstU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortThird

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete inverse-triality packet: a Z vector or sixty-four actual octad coefficients. -/
noncomputable def monsterNortonLine02ThirdPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonLine02FirstUIsOdd k then
    trialityXYZBasis 2 (finProdFinEquiv (monsterNortonLine02FirstUOddCode k,
      monsterNortonLine02FirstUOddPosition k))
  else
    monsterNortonOctadShortVector
      (monsterNortonOctadIndex (monsterNortonLine02FirstUOctadCodes k)
        (monsterNortonLine02FirstUOctad_weight k))
      (fun r => (monsterNortonOctadInverseCoefficient r
        (monsterNortonLine02FirstUOctadSign k) : ℝ) / 8)

/-- Inverse triality sends every actual reached U unit to the complete stated packet. -/
theorem monsterNortonLine02ThirdPacket_actual (k : Fin 23) :
    sExtra.symm (monsterNortonPureShort (monsterNortonLine02FirstUOutput k)) =
      monsterNortonLine02ThirdPacket k := by
  unfold monsterNortonLine02FirstUOutput monsterNortonLine02ThirdPacket
  by_cases h : monsterNortonLine02FirstUIsOdd k = true
  · simp only [ite_eq_left h]
    exact monsterNortonOddShort_extra_inverse _ _
  · simp only [ite_eq_right h]
    unfold monsterNortonPureShort
    rw [← monsterNortonOctadShortVector_single _ _ 1,
      monsterNortonOctadShortVector_extra_inverse]
    congr 1
    funext r
    rw [monsterNortonOctadTriality_inverse_single, mul_one]

/-- The combined true V and squared-U phases, including all exceptional negative outputs. -/
def monsterNortonLine02FirstThreePhase (k : Fin 23) : ZMod 2 :=
  monsterNortonEvenShortInitialVPhase k + monsterNortonLine02FirstUPhase k

/-- Entire literal V, squared-U, inverse-triality transport of all twenty-three preferred units. -/
theorem monsterNortonLine02FirstThree_actual (k : Fin 23) :
    sExtra.symm ((y555NortonActualU ^ 2).val (y555NortonV.val
      (monsterNortonPureShort (monsterNortonEvenShortBasis k)))) =
      qSign (monsterNortonLine02FirstThreePhase k) • monsterNortonLine02ThirdPacket k := by
  rw [monsterNortonEvenShortInitialV_actual, map_smul,
    monsterNortonLine02FirstU_actual, map_smul, map_smul,
    monsterNortonLine02ThirdPacket_actual, smul_smul]
  rw [monsterNortonLine02FirstThreePhase, qSign_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

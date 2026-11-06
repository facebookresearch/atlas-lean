/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual U image of the sparse second-input forward half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Actual input scalar of every short unit in the half packet, with its original denominator. -/
noncomputable def monsterNortonSecondHalfShortCoefficient : NortonSecondHalfShortIndex → ℝ
  | Sum.inl _ => -1 / 16
  | Sum.inr (d, e) => (monsterNortonSecondHalfOctadCoefficient d e : ℝ) / 16

/-- The complete pure-matrix part after actual U, as eight actual transported source A units. -/
noncomputable def monsterNortonSecondHalfUMatrixPacket : GriessSpace :=
  ∑ i : Fin 8, ((monsterNortonSecondHalfPairCoefficient i : ℝ) / 16) •
    griessConwayDecode (conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonSecondHalfPairIndex i)), (0, 0))

/-- The complete short part after actual U, as 240 phase-checked original preferred units. -/
noncomputable def monsterNortonSecondHalfUShortPacket : GriessSpace :=
  ∑ i : NortonSecondHalfShortIndex, monsterNortonSecondHalfShortCoefficient i •
    monsterNortonPureShort (monsterNortonSecondHalfShortUOutput i)

private theorem pair_C (p : Fin 276) :
    trialityABCBasis 2 p = ∑ s : Fin 2, monsterNortonPureShort (Sum.inl (s, p)) := by
  rw [Fin.sum_univ_two, monsterNortonPairShort_ABC, monsterNortonPairShort_ABC]
  norm_num
  module

private theorem pair_C_U (i : Fin 8) :
    y555NortonActualU.val (trialityABCBasis 2 (monsterNortonSecondHalfPairIndex i)) =
      ∑ s : Fin 2, monsterNortonPureShort
        (monsterNortonSecondHalfShortUOutput (Sum.inl (i, s))) := by
  rw [pair_C, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact monsterNortonSecondHalfU_short_actual (Sum.inl (i, s))

/-- Actual U sends the entire sparse half packet to its complete matrix and short packets. -/
theorem monsterNortonSecondHalfUWhole_actual :
    y555NortonActualU.val monsterNortonSecondHalfPacket =
      monsterNortonSecondHalfUMatrixPacket + monsterNortonSecondHalfUShortPacket := by
  have ho (d : Fin 14) (e : Fin 16) :
      y555NortonActualU.val (monsterNortonPureShort
        (Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonSecondHalfOctadCode d)
          (monsterNortonSecondHalfOctad_weight d), monsterNortonSecondHalfOctadSign d e)))) =
        monsterNortonPureShort (monsterNortonSecondHalfShortUOutput (Sum.inr (d, e))) :=
    monsterNortonSecondHalfU_short_actual (Sum.inr (d, e))
  unfold monsterNortonSecondHalfPacket
  simp only [Fintype.sum_sum_type, map_add, map_sum, map_smul,
    monsterNortonSecondHalfCoefficient, monsterNortonSecondHalfVector,
    monsterNortonU_pair_matrix, pair_C_U]
  unfold monsterNortonSecondHalfUMatrixPacket monsterNortonSecondHalfUShortPacket
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
    monsterNortonSecondHalfShortCoefficient, Finset.smul_sum]
  simp_rw [ho]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

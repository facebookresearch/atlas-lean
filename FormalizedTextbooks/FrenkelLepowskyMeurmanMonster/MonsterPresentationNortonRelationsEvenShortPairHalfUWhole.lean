/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual U images of the twelve phase-checked sparse forward-half candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPool
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUWholeData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every supported candidate unit has its whole actual positive-phase preferred U image. -/
theorem monsterNortonPairHalfU_short_actual (k : Fin 12) (i : NortonPairHalfShortIndex) :
    y555NortonActualU.val (monsterNortonPureShort (monsterNortonPairHalfShortInput k i)) =
      monsterNortonPureShort (monsterNortonPairHalfShortUOutput k i) := by
  rw [← monsterNortonPairHalfUPoolLookup_actual]
  exact monsterNortonPairHalfUPool_actual (monsterNortonPairHalfUPoolStorage k i)

private theorem pair_C (p : Fin 276) :
    trialityABCBasis 2 p = ∑ s : Fin 2, monsterNortonPureShort (Sum.inl (s, p)) := by
  rw [Fin.sum_univ_two, monsterNortonPairShort_ABC, monsterNortonPairShort_ABC]
  norm_num
  module

private theorem pair_C_U (k : Fin 12) (p : Fin 8) :
    y555NortonActualU.val (trialityABCBasis 2 (monsterNortonPairHalfPairIndex k p)) =
      ∑ s : Fin 2, monsterNortonPureShort
        (monsterNortonPairHalfShortUOutput k (Sum.inl (p, s))) := by
  rw [pair_C, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact monsterNortonPairHalfU_short_actual k (Sum.inl (p, s))

/-- Whole actual U transports each candidate to its complete matrix and short packets. -/
theorem monsterNortonPairHalfUWhole_actual (k : Fin 12) :
    y555NortonActualU.val (monsterNortonPairHalfPacket k) =
      monsterNortonPairHalfUMatrixPacket k + monsterNortonPairHalfUShortPacket k := by
  have ho (d : Fin 14) (e : Fin 16) :
      y555NortonActualU.val (monsterNortonPureShort
        (Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonPairHalfOctadCode k d)
          (monsterNortonPairHalfOctad_weight k d), monsterNortonPairHalfOctadSign k d e)))) =
        monsterNortonPureShort (monsterNortonPairHalfShortUOutput k (Sum.inr (d, e))) :=
    monsterNortonPairHalfU_short_actual k (Sum.inr (d, e))
  unfold monsterNortonPairHalfPacket
  simp only [Fintype.sum_sum_type, map_add, map_sum, map_smul,
    monsterNortonPairHalfCoefficient, monsterNortonPairHalfVector,
    monsterNortonU_pair_matrix, pair_C_U]
  unfold monsterNortonPairHalfUMatrixPacket monsterNortonPairHalfUShortPacket
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
    monsterNortonPairHalfShortCoefficient, Finset.smul_sum]
  simp_rw [ho]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete actual physical matrix after the eighth first-pair word operator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem u_matrix_projection (x : GriessSpace) :
    monsterNortonMatrixProjection (y555NortonActualU.val x) =
      conwayMatrixAction monsterNortonUFiber.val.2 (monsterNortonMatrixProjection x) := by
  rw [← monsterNortonULocal_generated]
  change (griessConwayEncode (localGriessRepresentation monsterNortonUFiber x)).1 =
    conwayMatrixAction monsterNortonUFiber.val.2 (griessConwayEncode x).1
  have h := congrArg (fun z : ConwayRawSpace => z.1)
    (localGriessRepresentation_encode monsterNortonUFiber x)
  rw [localConwayRawRepresentation_apply] at h
  exact h

/-- Every actual eighth-state matrix entry has this exact phase-complete integer numerator. -/
theorem monsterNortonLine01PairEighth_matrix (i j : Fin 24) :
    monsterNortonMatrixProjection (y555NortonActualU.val monsterNortonLine01PairAfterSeventh)
      i j =
      ((∑ e : Fin 64, if monsterNortonLine01PairInverseIsPair e then
        monsterNortonLine01PairSixthNumerator e *
          monsterNortonUPairMatrixNumerator (monsterNortonLine01PairInversePhysicalPair e) i j
        else 0 : ℤ) : ℝ) / 256 := by
  rw [u_matrix_projection, monsterNortonLine01PairSeventh_matrix, map_sum]
  rw [Matrix.sum_apply]
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : monsterNortonLine01PairInverseIsPair e = true
  · simp only [ite_eq_left h, map_smul, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [monsterNortonUPairMatrix_coordinates]
    ring
  · simp only [ite_eq_right h, map_zero, Matrix.zero_apply, Int.cast_zero, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

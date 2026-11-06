/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual eighth matrix constituent is exactly the certified physical diagonal vector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthMatrixData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Integer numerators of all original physical diagonal entries after the eighth operator. -/
def monsterNortonLine01PairEighthDiagonalNumerator : Fin 24 → ℤ :=
  ![-1, 1, 0, 0, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 0, 0, -1, 0, 0, 1, -1, 0, 1, 0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Verify every entry from the eight actual transported source pairs.
/-- The eight actual source-column contributions give exactly this entire diagonal matrix. -/
theorem monsterNortonLine01PairEighthDiagonal_certificate (i j : Fin 24) :
    (∑ k : Fin 8, monsterNortonLine01PairSeventhMatrixNumerator k *
      (monsterNortonUNumerator1 i ⟨2 * k.val, by omega⟩ *
        monsterNortonUNumerator1 j ⟨2 * k.val + 1, by omega⟩ +
      monsterNortonUNumerator1 i ⟨2 * k.val + 1, by omega⟩ *
        monsterNortonUNumerator1 j ⟨2 * k.val, by omega⟩)) =
      16 * (if i = j then monsterNortonLine01PairEighthDiagonalNumerator i else 0) := by
  revert i j
  decide +kernel

private theorem adjacentNumerator (k : Fin 8) (i j : Fin 24) :
    monsterNortonUPairMatrixNumerator (monsterNortonLine01AdjacentPair k) i j =
      monsterNortonUNumerator1 i ⟨2 * k.val, by omega⟩ *
        monsterNortonUNumerator1 j ⟨2 * k.val + 1, by omega⟩ +
      monsterNortonUNumerator1 i ⟨2 * k.val + 1, by omega⟩ *
        monsterNortonUNumerator1 j ⟨2 * k.val, by omega⟩ := by
  rw [monsterNortonUPairMatrixNumerator, monsterNortonLine01AdjacentPair_coordinates]

/-- The complete actual transported matrix sum has the certified diagonal coordinates. -/
theorem monsterNortonLine01PairEighthDiagonal_matrix :
    (∑ k : Fin 8, ((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
      conwayMatrixAction monsterNortonUFiber.val.2
        (trialityPairMatrix (monsterNortonLine01AdjacentPair k))) =
      Matrix.diagonal (fun i => (monsterNortonLine01PairEighthDiagonalNumerator i : ℝ) / 16) := by
  funext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, monsterNortonUPairMatrix_coordinates,
    adjacentNumerator]
  calc
    _ = ((∑ k : Fin 8, monsterNortonLine01PairSeventhMatrixNumerator k *
      (monsterNortonUNumerator1 i ⟨2 * k.val, by omega⟩ *
        monsterNortonUNumerator1 j ⟨2 * k.val + 1, by omega⟩ +
      monsterNortonUNumerator1 i ⟨2 * k.val + 1, by omega⟩ *
        monsterNortonUNumerator1 j ⟨2 * k.val, by omega⟩) : ℤ) : ℝ) / 256 := by
      rw [Int.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    _ = _ := by
      rw [monsterNortonLine01PairEighthDiagonal_certificate]
      simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_ite, Int.cast_zero,
        Matrix.diagonal_apply]
      by_cases h : i = j
      · simp [h]
        ring
      · simp [h]

private def matrixRawLift : Matrix (Fin 24) (Fin 24) ℝ →ₗ[ℝ] ConwayRawSpace where
  toFun A := (A, (0, 0))
  map_add' _A _B := Prod.ext rfl (Prod.ext (zero_add 0).symm (zero_add 0).symm)
  map_smul' c _A := Prod.ext rfl (Prod.ext (smul_zero c).symm (smul_zero c).symm)

private noncomputable def matrixLift : Matrix (Fin 24) (Fin 24) ℝ →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp matrixRawLift

/-- The entire eighth vector is a fixed diagonal-matrix component plus the actual short packet. -/
theorem monsterNortonLine01PairEighth_diagonal :
    y555NortonActualU.val monsterNortonLine01PairAfterSeventh =
      griessConwayDecode (Matrix.diagonal
        (fun i => (monsterNortonLine01PairEighthDiagonalNumerator i : ℝ) / 16), (0, 0)) +
      monsterNortonLine01PairEighthShortPacket := by
  rw [monsterNortonLine01PairEighth_sparse]
  have hm : (∑ k : Fin 8, ((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
      griessConwayDecode (conwayMatrixAction monsterNortonUFiber.val.2
        (trialityPairMatrix (monsterNortonLine01AdjacentPair k)), (0, 0))) =
      griessConwayDecode (Matrix.diagonal
        (fun i => (monsterNortonLine01PairEighthDiagonalNumerator i : ℝ) / 16), (0, 0)) := by
    change (∑ k : Fin 8, ((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
      matrixLift (conwayMatrixAction monsterNortonUFiber.val.2
        (trialityPairMatrix (monsterNortonLine01AdjacentPair k)))) = matrixLift _
    calc
      _ = ∑ k : Fin 8, matrixLift
          (((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
            conwayMatrixAction monsterNortonUFiber.val.2
              (trialityPairMatrix (monsterNortonLine01AdjacentPair k))) := by
        apply Finset.sum_congr rfl
        intro k _
        exact (matrixLift.map_smul _ _).symm
      _ = matrixLift (∑ k : Fin 8,
          ((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
            conwayMatrixAction monsterNortonUFiber.val.2
              (trialityPairMatrix (monsterNortonLine01AdjacentPair k))) :=
        (map_sum matrixLift _ _).symm
      _ = _ := by rw [monsterNortonLine01PairEighthDiagonal_matrix]
  rw [hm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

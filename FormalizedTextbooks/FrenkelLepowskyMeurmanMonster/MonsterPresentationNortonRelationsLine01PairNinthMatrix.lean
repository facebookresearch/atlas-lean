/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The entire true ninth matrix contribution is minus one half of an actual forward-U image. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairNinthMatrixData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem physicalPairEntry (k : Fin 240) (i j : Fin 24) :
    trialityPairMatrix (monsterNortonLine01PairEighthPhysicalPair k) i j =
      (((if i = monsterNortonLine01PairEighthPairFirst k ∧
          j = monsterNortonLine01PairEighthPairSecond k then (1 : ℤ) else 0) +
        (if i = monsterNortonLine01PairEighthPairSecond k ∧
          j = monsterNortonLine01PairEighthPairFirst k then (1 : ℤ) else 0)) : ℝ) := by
  have hc : griessCoordinatePair (monsterNortonLine01PairEighthPhysicalPair k) =
      (monsterNortonLine01PairEighthPairFirst k,
        monsterNortonLine01PairEighthPairSecond k) := by
    rw [monsterNortonLine01PairEighthPhysicalPair, griessPairIndex_coordinates]
    simp only [monsterNortonLine01PairEighthPair_increasing, ite_true]
  simp only [trialityPairMatrix, hc, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply,
    Int.cast_ite, Int.cast_one, Int.cast_zero]
  by_cases hif : i = monsterNortonLine01PairEighthPairFirst k <;>
    by_cases his : i = monsterNortonLine01PairEighthPairSecond k <;>
    by_cases hjf : j = monsterNortonLine01PairEighthPairFirst k <;>
    by_cases hjs : j = monsterNortonLine01PairEighthPairSecond k <;>
    simp [hif, his, hjf, hjs, eq_comm]

private theorem firstPairNumerator (i j : Fin 24) :
    monsterNortonUPairMatrixNumerator (monsterNortonLine01AdjacentPair 0) i j =
      monsterNortonUNumerator1 i 0 * monsterNortonUNumerator1 j 1 +
        monsterNortonUNumerator1 i 1 * monsterNortonUNumerator1 j 0 := by
  rw [monsterNortonUPairMatrixNumerator, monsterNortonLine01AdjacentPair_coordinates]
  rfl

/-- The entire actual ninth physical matrix equals a scalar multiple of the true U matrix image. -/
theorem monsterNortonLine01PairNinth_matrix_U :
    Matrix.diagonal (fun i => (monsterNortonLine01PairEighthDiagonalNumerator i : ℝ) / 16) +
      (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
        (((monsterNortonLine01PairEighthCoefficient k *
          (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) /
            32) • trialityPairMatrix (monsterNortonLine01PairEighthPhysicalPair k) else 0) =
      (-1 / 2 : ℝ) • conwayMatrixAction monsterNortonUFiber.val.2
        (trialityPairMatrix (monsterNortonLine01AdjacentPair 0)) := by
  funext i j
  calc
    _ = ((2 * (if i = j then monsterNortonLine01PairEighthDiagonalNumerator i else 0) +
      (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
        monsterNortonLine01PairEighthCoefficient k *
          (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) *
          ((if i = monsterNortonLine01PairEighthPairFirst k ∧
              j = monsterNortonLine01PairEighthPairSecond k then (1 : ℤ) else 0) +
            (if i = monsterNortonLine01PairEighthPairSecond k ∧
              j = monsterNortonLine01PairEighthPairFirst k then (1 : ℤ) else 0))
        else 0) : ℤ) : ℝ) / 32 := by
      rw [Int.cast_add, add_div]
      simp only [Matrix.add_apply, Matrix.diagonal_apply, Matrix.sum_apply]
      congr 1
      · rw [Int.cast_mul, Int.cast_ofNat, Int.cast_ite, Int.cast_zero]
        by_cases h : i = j
        · simp [h]
          ring
        · simp [h]
      · rw [Int.cast_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hp : monsterNortonLine01PairEighthIsPair k = true
        · rw [ite_eq_left hp, ite_eq_left hp, Matrix.smul_apply, smul_eq_mul,
            physicalPairEntry, Int.cast_mul]
          push_cast
          ring
        · rw [ite_eq_right hp, ite_eq_right hp]
          simp
    _ = (monsterNortonLine01PairNinthMatrixNumerator i j : ℝ) / 16 := by
      rw [monsterNortonLine01PairNinthMatrixNumerator_certificate, Int.cast_mul,
        Int.cast_ofNat]
      ring
    _ = _ := by
      rw [Matrix.smul_apply, smul_eq_mul, monsterNortonUPairMatrix_coordinates,
        firstPairNumerator, monsterNortonLine01PairNinthMatrixU_certificate]
      push_cast
      ring

private def matrixRawLift : Matrix (Fin 24) (Fin 24) ℝ →ₗ[ℝ] ConwayRawSpace where
  toFun A := (A, (0, 0))
  map_add' _A _B := Prod.ext rfl (Prod.ext (zero_add 0).symm (zero_add 0).symm)
  map_smul' c _A := Prod.ext rfl (Prod.ext (smul_zero c).symm (smul_zero c).symm)

private noncomputable def matrixLift : Matrix (Fin 24) (Fin 24) ℝ →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp matrixRawLift

private theorem matrixLiftABC (p : Fin 276) :
    matrixLift (trialityPairMatrix p) = trialityABCBasis 0 p := by
  change griessConwayDecode (trialityPairMatrix p, (0, 0)) = _
  rw [← griessConwayEncode_ABC_zero_sparse, griessConwayDecode_encode]

/-- The full ninth matrix-only Griess vector has its actual forward-U equality on all blocks. -/
theorem monsterNortonLine01PairNinth_matrix_vector_U :
    griessConwayDecode (Matrix.diagonal
      (fun i => (monsterNortonLine01PairEighthDiagonalNumerator i : ℝ) / 16), (0, 0)) +
      (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
        (((monsterNortonLine01PairEighthCoefficient k *
          (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) /
            32) • trialityABCBasis 0 (monsterNortonLine01PairEighthPhysicalPair k) else 0) =
      (-1 / 2 : ℝ) • y555NortonActualU.val
        (trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0)) := by
  simp only [← matrixLiftABC]
  change matrixLift _ + (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
    (((monsterNortonLine01PairEighthCoefficient k *
      (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) / 32) •
        matrixLift (trialityPairMatrix (monsterNortonLine01PairEighthPhysicalPair k)) else 0) = _
  have hs : (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
      (((monsterNortonLine01PairEighthCoefficient k *
        (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) / 32) •
        matrixLift (trialityPairMatrix (monsterNortonLine01PairEighthPhysicalPair k)) else 0) =
      matrixLift (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
        (((monsterNortonLine01PairEighthCoefficient k *
          (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) /
            32) • trialityPairMatrix (monsterNortonLine01PairEighthPhysicalPair k) else 0) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hp : monsterNortonLine01PairEighthIsPair k = true
    · rw [ite_eq_left hp, ite_eq_left hp, map_smul]
    · rw [ite_eq_right hp, ite_eq_right hp, map_zero]
  rw [hs, ← matrixLift.map_add, monsterNortonLine01PairNinth_matrix_U, map_smul]
  rw [matrixLiftABC, monsterNortonU_pair_matrix]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

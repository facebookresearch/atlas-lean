/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhSeventhMatrixFrameData

/-! Every physical frame coefficient and complete matrix congruence comes from actual isometries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The complete frame is a product of three genuine original Leech lattice isometries. -/
def generatedEleventhSeventhMatrixFrame : leechIsomSubgroup :=
  golayPermutationIsometry generatedEleventhSeventhFramePermutation *
    golaySignIsometry (sourceGeneratedSignCode 32) * co1XiIsometry

/-- Every actual physical frame coordinate has exactly its checked original integer numerator. -/
theorem generatedEleventh_seventh_matrix_frame_actual :
    leechIsomMatrix generatedEleventhSeventhMatrixFrame =
      (1 / 2 : ℝ) • generatedEleventhSeventhFrameNumerator.map (Int.castRingHom ℝ) := by
  ext i j
  change golayRealPermute generatedEleventhSeventhFramePermutation.val
      (golayRealSign (sourceGeneratedSignCode 32).val (co1XiEquiv (Pi.single j 1))) i = _
  rw [golayRealPermute_apply, golayRealSign_apply,
    (generatedEleventh_seventh_frame_permutation i).2]
  change qSign ((sourceGeneratedSignCode 32).val (generatedEleventhSeventhFrameBackward i)) *
    leechIsomMatrix co1XiIsometry (generatedEleventhSeventhFrameBackward i) j = _
  rw [generatedEleventh_xi_physical_matrix]
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    generatedEleventh_seventh_frame_numerator]
  by_cases h : (sourceGeneratedSignCode 32).val (generatedEleventhSeventhFrameBackward i) = 0 <;>
    simp [qSign, h]

/-- The entire original integer matrix congruence remains valid in the actual physical space. -/
theorem generatedEleventh_seventh_frame_real :
    generatedEleventhSeventhFrameNumerator.map (Int.castRingHom ℝ) *
      generatedEleventhMatrixNumerator.map (Int.castRingHom ℝ) *
        (generatedEleventhSeventhFrameNumerator.map (Int.castRingHom ℝ)).transpose =
      (4 : ℕ) • generatedSeventhMatrixNumerator.map (Int.castRingHom ℝ) := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix generatedEleventh_seventh_frame_integer
  simp only [map_mul, map_nsmul] at h
  simpa only [RingHom.mapMatrix_apply, Matrix.transpose_map] using h

/-- A genuine original lattice frame matches all actual matrix entries without a class inference. -/
theorem generatedEleventh_seventh_matrix_conjugation :
    conwayMatrixAction generatedEleventhSeventhMatrixFrame
        (griessConwayEncode generatedEleventhAxis).1 =
      (griessConwayEncode generatedSeventhAxis).1 := by
  have hn : (griessConwayEncode generatedEleventhAxis).1 =
      (1 / 32 : ℝ) • generatedEleventhMatrixNumerator.map (Int.castRingHom ℝ) := by
    rw [generatedEleventh_matrix_actual]
    ext i j
    change (generatedEleventhMatrixNumerator i j : ℝ) / 32 =
      (1 / 32 : ℝ) * (generatedEleventhMatrixNumerator i j : ℝ)
    ring
  rw [conwayMatrixAction_eq_conjugate, generatedEleventh_seventh_matrix_frame_actual, hn,
    Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    mul_smul_comm, smul_mul_assoc, generatedEleventh_seventh_frame_real]
  rw [generatedSeventh_axis_matrix, generatedSeventh_matrix_numerator_real]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    generatedSeventhMatrixIntegerReal]
  norm_num [Pi.smul_apply, nsmul_eq_mul]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

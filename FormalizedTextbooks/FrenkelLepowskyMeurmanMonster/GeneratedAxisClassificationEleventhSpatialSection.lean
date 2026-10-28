/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiMatrix

/-! The genuine eight-dimensional spatial section is recovered in all physical coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Four times the original actual eight-dimensional projection, including its off-diagonal rows. -/
def generatedEleventhSectionInteger : Matrix (Fin 24) (Fin 24) ℤ := ![
  ![1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 3, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 3, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1]
]

/-- The integer affine expression in the complete actual matrix. -/
def generatedEleventhCenteredInteger : Matrix (Fin 24) (Fin 24) ℤ :=
  generatedEleventhMatrixNumerator - (9 : ℕ) • 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check the full actual matrix polynomial, retaining every off-diagonal coordinate.
/-- A polynomial recovers the original spatial projector. -/
theorem generatedEleventh_centered_integer_polynomial :
    generatedEleventhCenteredInteger * generatedEleventhCenteredInteger -
      (4 : ℕ) • generatedEleventhCenteredInteger = (8 : ℕ) • generatedEleventhSectionInteger := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check the actual original Xi conjugator against every physical coordinate.
/-- The original Xi carries this actual projection to the genuine coordinate octad 1345. -/
theorem generatedEleventh_section_xi_integer :
    co1XiNumerator * generatedEleventhSectionInteger * co1XiNumerator.transpose =
      (16 : ℕ) • Matrix.diagonal (fun i => if Nat.testBit 0x22e122 i.val then 1 else 0) := by
  decide +kernel

/-- The real actual eight-dimensional projection recovered by the matrix polynomial. -/
def generatedEleventhCoordinateSection : Matrix (Fin 24) (Fin 24) ℝ :=
  (1 / 4 : ℝ) • generatedEleventhSectionInteger.map (Int.castRingHom ℝ)

/-- The real affine expression in the complete original matrix. -/
def generatedEleventhCenteredMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedEleventhMatrixNumerator.map (Int.castRingHom ℝ) - (9 : ℕ) • 1

/-- The integer source polynomial gives the actual real projection polynomial. -/
theorem generatedEleventh_centered_polynomial :
    generatedEleventhCenteredMatrix * generatedEleventhCenteredMatrix -
      (4 : ℕ) • generatedEleventhCenteredMatrix =
        (32 : ℝ) • generatedEleventhCoordinateSection := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix generatedEleventh_centered_integer_polynomial
  simp only [generatedEleventhCenteredInteger, map_sub, map_mul, map_nsmul, map_one] at h
  have h' : generatedEleventhCenteredMatrix * generatedEleventhCenteredMatrix -
      (4 : ℕ) • generatedEleventhCenteredMatrix =
        (8 : ℕ) • generatedEleventhSectionInteger.map (Int.castRingHom ℝ) := h
  rw [h', generatedEleventhCoordinateSection, smul_smul]
  ext i j
  change (8 : ℕ) • ((generatedEleventhSectionInteger i j : ℤ) : ℝ) = _
  simp only [nsmul_eq_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  norm_num

/-- The centered real matrix is the exact original affine expression in the axis matrix. -/
theorem generatedEleventh_centered_matrix_actual :
    generatedEleventhCenteredMatrix =
      (32 : ℝ) • (griessConwayEncode generatedEleventhAxis).1 - (9 : ℕ) • 1 := by
  rw [generatedEleventh_matrix_actual]
  ext i j
  simp only [generatedEleventhCenteredMatrix, Matrix.sub_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  change (generatedEleventhMatrixNumerator i j : ℝ) - _ = _
  ring

/-- Fixing the complete actual matrix preserves its original spatial eight-dimensional section. -/
theorem generatedEleventh_matrix_fix_section (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedEleventhAxis).1 =
      (griessConwayEncode generatedEleventhAxis).1) :
    conwayMatrixAction g generatedEleventhCoordinateSection =
      generatedEleventhCoordinateSection := by
  have hB : conwayMatrixAction g generatedEleventhCenteredMatrix =
      generatedEleventhCenteredMatrix := by
    rw [generatedEleventh_centered_matrix_actual]
    rw [map_sub, map_smul, map_nsmul, conwayMatrixAction_one, hg]
  have h32 : (32 : ℝ) • conwayMatrixAction g generatedEleventhCoordinateSection =
      (32 : ℝ) • generatedEleventhCoordinateSection := by
    calc
      _ = conwayMatrixAction g ((32 : ℝ) • generatedEleventhCoordinateSection) :=
        (map_smul _ _ _).symm
      _ = conwayMatrixAction g (generatedEleventhCenteredMatrix * generatedEleventhCenteredMatrix -
          (4 : ℕ) • generatedEleventhCenteredMatrix) :=
        congrArg _ generatedEleventh_centered_polynomial.symm
      _ = generatedEleventhCenteredMatrix * generatedEleventhCenteredMatrix -
          (4 : ℕ) • generatedEleventhCenteredMatrix := by
        rw [map_sub, conwayMatrixAction_mul, map_nsmul, hB]
      _ = (32 : ℝ) • generatedEleventhCoordinateSection := generatedEleventh_centered_polynomial
  exact (smul_right_injective _ (by norm_num : (32 : ℝ) ≠ 0)) h32

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

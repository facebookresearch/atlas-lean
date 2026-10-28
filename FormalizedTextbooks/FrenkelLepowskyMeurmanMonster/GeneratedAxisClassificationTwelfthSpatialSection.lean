/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagMatrix

/-! A polynomial recovers the genuine coordinate-octad section from the complete actual matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original coordinate-octad projector, in integer physical coordinates. -/
def generatedTwelfthSectionInteger : Matrix (Fin 24) (Fin 24) ℤ :=
  Matrix.diagonal (fun i => if Nat.testBit 0x0f000f i.val then 1 else 0)

/-- The integer matrix on the genuine distinguished eight-dimensional section. -/
def generatedTwelfthGoldenInteger : Matrix (Fin 24) (Fin 24) ℤ :=
  generatedTwelfthMatrixNumerator - (5 : ℕ) • 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- All integer polynomial entries are checked against the original certified actual matrix.
/-- A polynomial extracts precisely the original coordinate-octad projector. -/
theorem generatedTwelfth_golden_integer_polynomial :
    generatedTwelfthGoldenInteger * generatedTwelfthGoldenInteger -
      (2 : ℕ) • generatedTwelfthGoldenInteger = (4 : ℕ) • generatedTwelfthSectionInteger := by
  decide +kernel

/-- The real projection onto the actual physical coordinate-octad section. -/
def generatedTwelfthCoordinateSection : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedTwelfthSectionInteger.map (Int.castRingHom ℝ)

/-- The real golden matrix, retaining the full original physical coordinate entries. -/
def generatedTwelfthGoldenMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedTwelfthMatrixNumerator.map (Int.castRingHom ℝ) - (5 : ℕ) • 1

/-- The exact original integer polynomial remains valid on the actual real matrix coordinates. -/
theorem generatedTwelfth_golden_polynomial :
    generatedTwelfthGoldenMatrix * generatedTwelfthGoldenMatrix -
      (2 : ℕ) • generatedTwelfthGoldenMatrix = (4 : ℕ) • generatedTwelfthCoordinateSection := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix generatedTwelfth_golden_integer_polynomial
  simp only [generatedTwelfthGoldenInteger, map_sub, map_mul, map_nsmul, map_one] at h
  exact h

/-- The golden matrix is the exact scalar affine expression in the entire original axis matrix. -/
theorem generatedTwelfth_golden_matrix_actual :
    generatedTwelfthGoldenMatrix =
      (16 : ℝ) • (griessConwayEncode generatedTwelfthAxis).1 - (5 : ℕ) • 1 := by
  rw [generatedTwelfth_matrix_actual]
  ext i j
  simp only [generatedTwelfthGoldenMatrix, Matrix.sub_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  change (generatedTwelfthMatrixNumerator i j : ℝ) - _ = _
  ring

/-- Every genuine spatial isometry fixing the actual matrix fixes its original octad section. -/
theorem generatedTwelfth_matrix_fix_section (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedTwelfthAxis).1 =
      (griessConwayEncode generatedTwelfthAxis).1) :
    conwayMatrixAction g generatedTwelfthCoordinateSection = generatedTwelfthCoordinateSection := by
  have hB : conwayMatrixAction g generatedTwelfthGoldenMatrix = generatedTwelfthGoldenMatrix := by
    rw [generatedTwelfth_golden_matrix_actual]
    rw [map_sub, map_smul, map_nsmul, conwayMatrixAction_one, hg]
  have h4 : (4 : ℕ) • conwayMatrixAction g generatedTwelfthCoordinateSection =
      (4 : ℕ) • generatedTwelfthCoordinateSection := by
    calc
      _ = conwayMatrixAction g ((4 : ℕ) • generatedTwelfthCoordinateSection) :=
        (map_nsmul _ _ _).symm
      _ = conwayMatrixAction g (generatedTwelfthGoldenMatrix * generatedTwelfthGoldenMatrix -
          (2 : ℕ) • generatedTwelfthGoldenMatrix) :=
        congrArg _ generatedTwelfth_golden_polynomial.symm
      _ = generatedTwelfthGoldenMatrix * generatedTwelfthGoldenMatrix -
          (2 : ℕ) • generatedTwelfthGoldenMatrix := by
        rw [map_sub, conwayMatrixAction_mul, map_nsmul, hB]
      _ = (4 : ℕ) • generatedTwelfthCoordinateSection := generatedTwelfth_golden_polynomial
  ext i j
  have h := congrFun (congrFun h4 i) j
  change (4 : ℕ) • (conwayMatrixAction g generatedTwelfthCoordinateSection i j) =
    (4 : ℕ) • generatedTwelfthCoordinateSection i j at h
  simp only [nsmul_eq_mul] at h
  norm_num at h
  linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

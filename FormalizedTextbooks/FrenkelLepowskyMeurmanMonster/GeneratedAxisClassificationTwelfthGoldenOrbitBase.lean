/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionMatrices

/-! The finite golden orbit has the complete original actual axis matrix as its genuine base. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The integer rectangular insertion of the original physical octad coordinates. -/
def generatedTwelfthSectionInsertionInteger : Matrix (Fin 24) (Fin 8) ℤ := fun i j =>
  if i = generatedFifthFramePositions j then 1 else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check every full ambient integer entry against the original actual matrix numerator.
/-- The original complete actual centered matrix is the exact finite orbit base matrix. -/
theorem generatedTwelfthGoldenOrbit_base_integer :
    generatedTwelfthGoldenInteger =
      generatedTwelfthSectionInsertionInteger * generatedTwelfthGoldenMatrixState 18197 *
        generatedTwelfthSectionInsertionInteger.transpose := by
  decide +kernel

/-- The exact real rectangular insertion is the original integral insertion under casting. -/
theorem generatedTwelfthSectionInsertion_integer_real :
    generatedTwelfthSectionInsertionMatrix =
      generatedTwelfthSectionInsertionInteger.map (Int.castRingHom ℝ) := by
  ext i j
  change generatedTwelfthSectionInsertReal (Pi.single j 1) i = _
  fin_cases i <;> fin_cases j <;>
    norm_num [generatedTwelfthSectionInsertReal, generatedTwelfthSectionInsertionInteger,
      generatedFifthFramePositions, Pi.single_apply]

set_option maxRecDepth 20000 in
-- Check the exact distinct physical coordinate columns in the original integral insertion.
/-- The original octad insertion has orthonormal coordinate columns. -/
theorem generatedTwelfthSectionInsertion_integer_orthogonal :
    generatedTwelfthSectionInsertionInteger.transpose *
      generatedTwelfthSectionInsertionInteger = 1 := by
  decide +kernel

/-- The original real insertion retains all physical section matrices distinctly. -/
theorem generatedTwelfthSectionInsertion_orthogonal :
    generatedTwelfthSectionInsertionMatrix.transpose *
      generatedTwelfthSectionInsertionMatrix = 1 := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix
    generatedTwelfthSectionInsertion_integer_orthogonal
  simp only [map_one] at h
  change (generatedTwelfthSectionInsertionInteger.transpose *
    generatedTwelfthSectionInsertionInteger).map (Int.castRingHom ℝ) = 1 at h
  rw [Matrix.map_mul, Matrix.transpose_map] at h
  rw [generatedTwelfthSectionInsertion_integer_real]
  exact h

/-- The entire original ambient matrix insertion is injective. -/
theorem generatedTwelfthSectionMatrix_injective :
    Function.Injective generatedTwelfthSectionMatrix := by
  intro M N h
  have recover (A : Matrix (Fin 8) (Fin 8) ℝ) :
      generatedTwelfthSectionInsertionMatrix.transpose * generatedTwelfthSectionMatrix A *
        generatedTwelfthSectionInsertionMatrix = A := by
    unfold generatedTwelfthSectionMatrix
    calc
      _ = (generatedTwelfthSectionInsertionMatrix.transpose *
            generatedTwelfthSectionInsertionMatrix) * A *
          (generatedTwelfthSectionInsertionMatrix.transpose *
            generatedTwelfthSectionInsertionMatrix) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [generatedTwelfthSectionInsertion_orthogonal,
        Matrix.one_mul, Matrix.mul_one]
  have hh := congrArg (fun A => generatedTwelfthSectionInsertionMatrix.transpose *
    A * generatedTwelfthSectionInsertionMatrix) h
  rwa [recover M, recover N] at hh

/-- The original real golden matrix is the complete ambient insertion of the finite orbit base. -/
theorem generatedTwelfthGoldenOrbit_base_actual :
    generatedTwelfthGoldenMatrix = generatedTwelfthSectionMatrix
      ((generatedTwelfthGoldenMatrixState 18197).map (Int.castRingHom ℝ)) := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix generatedTwelfthGoldenOrbit_base_integer
  simp only [generatedTwelfthGoldenInteger, map_sub, map_nsmul, map_one] at h
  change generatedTwelfthGoldenMatrix =
    (generatedTwelfthSectionInsertionInteger * generatedTwelfthGoldenMatrixState 18197 *
      generatedTwelfthSectionInsertionInteger.transpose).map (Int.castRingHom ℝ) at h
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at h
  unfold generatedTwelfthSectionMatrix
  rw [generatedTwelfthSectionInsertion_integer_real]
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

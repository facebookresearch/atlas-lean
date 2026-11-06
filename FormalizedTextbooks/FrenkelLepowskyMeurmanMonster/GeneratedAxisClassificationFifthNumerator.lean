/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiData

/-! Finite original integer certificates for the fifth candidate's inverse spatial action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Genuine forward physical permutation matrices for the two frozen source generators. -/
def generatedFifthPermutationMatrix (k : Fin 2) : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if i = omegaOrbitPermForward k j then 1 else 0

/-- The exact composite of the two original physical permutation matrices. -/
def generatedFifthCompositePermutationMatrix : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if i = omegaOrbitPermForward 1 (omegaOrbitPermForward 0 j) then 1 else 0

/-- The named composite is exactly the product of the genuine source permutation matrices. -/
theorem generatedFifth_composite_permutation_certificate :
    generatedFifthCompositePermutationMatrix =
      generatedFifthPermutationMatrix 1 * generatedFifthPermutationMatrix 0 := by
  decide +kernel

/-- Four times the literal inverse spatial word Xi*P1*P0*Xi. -/
def generatedFifthInverseNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![0, 0, 0, 0, -1, 1, -1, -1, -1, 1, -1, -1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 1, -1, -1, 1, -1, 1, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 1, 1, -1, 1, -1, -1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 1, 1, 1, -1, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, -1, -1, 1, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2],
    ![0, 0, 0, 0, -1, -1, -1, 1, 1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0],
    ![0, 0, 0, 0, 1, 1, 1, -1, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0],
    ![0, 0, 0, 0, 1, 1, 1, -1, 1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2],
    ![0, 0, 0, 0, -1, -1, 1, -1, -1, -1, -1, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, -1, 1, -1, 1, 1, 1, -1, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, -1, 1, -1, -1, -1, 1, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, -1, 1, 1, 1, 1, -1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0],
    ![0, 0, 2, 2, -1, 1, 1, 1, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -2, 0, 0, 1, -1, -1, -1, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -2, 0, 0, -1, 1, 1, 1, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 2, 1, -1, -1, -1, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1, -1, -1, 1, -1, -1, 1, -1, -1],
    ![1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, 1, 1, -1, 1, -1, 1, -1, -1],
    ![1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1],
    ![1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1],
    ![1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1],
    ![1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1],
    ![1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1],
    ![1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, 1, -1]]

/-- The exact rational inverse matrix, with denominator four. -/
def generatedFifthInverseMatrixQ : Matrix (Fin 24) (Fin 24) ℚ :=
  generatedFifthInverseNumerator.map (fun z => (z : ℚ) / 4)

set_option maxHeartbeats 4000000 in
-- The small integer matrix is checked against the original Xi and permutation definitions.
theorem generatedFifth_inverse_numerator_certificate :
    generatedFifthInverseNumerator = co1XiNumerator * generatedFifthPermutationMatrix 1 *
      generatedFifthPermutationMatrix 0 * co1XiNumerator := by
  have h : generatedFifthInverseNumerator = co1XiNumerator *
      generatedFifthCompositePermutationMatrix * co1XiNumerator := by decide +kernel
  rw [generatedFifth_composite_permutation_certificate, ← Matrix.mul_assoc] at h
  exact h

set_option maxHeartbeats 8000000 in
-- The exact rational matrix retains both original source permutation orientations.
theorem generatedFifth_inverse_matrix_certificate :
    generatedFifthInverseMatrixQ = co1XiMatrixQ *
      (generatedFifthPermutationMatrix 1).map (Int.castRingHom ℚ) *
      (generatedFifthPermutationMatrix 0).map (Int.castRingHom ℚ) * co1XiMatrixQ := by
  have h : generatedFifthInverseMatrixQ = co1XiMatrixQ *
      generatedFifthCompositePermutationMatrix.map (Int.castRingHom ℚ) * co1XiMatrixQ := by
    decide +kernel
  rw [generatedFifth_composite_permutation_certificate, Matrix.map_mul, ← Matrix.mul_assoc] at h
  exact h

/-- Integer diagonal sums of the original transported coordinate-octad projection. -/
def generatedFifthProjectionDiagonal : Fin 24 → ℤ :=
  ![8, 8, 8, 8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 4, 4, 4, 4]

/-- The original inverse numerator gives every projection diagonal entry exactly. -/
theorem generatedFifth_projection_diagonal_certificate : ∀ i : Fin 24,
    (∑ j : Fin 24, if Nat.testBit 0xcccc00 j.val then
      generatedFifthInverseNumerator j i * generatedFifthInverseNumerator j i else 0) =
        generatedFifthProjectionDiagonal i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

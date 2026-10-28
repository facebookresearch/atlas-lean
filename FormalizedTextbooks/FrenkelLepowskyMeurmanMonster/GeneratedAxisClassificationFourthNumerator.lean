/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRepresentative

/-! Integer certificates for the physical inverse of the selected local word.
The displayed matrix is verified against the original Xi and permutation
matrices before any support certificate is used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- The actual positive source permutation in physical column convention. -/
def generatedFourthPermutationMatrix : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if i = omegaOrbitPermForward 0 j then 1 else 0

/-- Four times the inverse local spatial matrix, as a finite integer certificate. -/
def generatedFourthInverseNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![-1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, -1, -1, -1, 1, -1, -1, 1, -1],
  ![1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1],
  ![1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, -1, -1, -1, 1, 1, 1, -1, 1],
  ![-1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1],
  ![0, 0, 0, 0, -1, -3, 1, 1, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, -1, 3, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, 3, -1, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 3, 1, 1, 1, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, 1, 1, 1, -1, -3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, -1, -1, 1, -1, 3, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, -1, -1, -1, 1, -1, -1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, 1, 1, 1, 3, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1, -1, 1, 1, 1, -1, 1, 1, 1],
  ![1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, 1],
  ![1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1],
  ![-1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1],
  ![1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1, -1, -1, 1, -1, -1, 1, -1, -1],
  ![1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, 1, 1, -1, 1, -1, 1, -1, -1],
  ![1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1],
  ![1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1],
  ![1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1],
  ![1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1],
  ![1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, 1, -1],
  ![1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1]]

set_option maxHeartbeats 12000000 in
-- Verify all 576 integer entries of the source matrix product.
/-- The certificate is exactly the original product Xi, P0, Xi. -/
theorem generatedFourth_inverse_numerator_certificate :
    generatedFourthInverseNumerator =
      co1XiNumerator * generatedFourthPermutationMatrix * co1XiNumerator := by
  decide +kernel

/-- An integral preferred pair vector, with increasing coordinates supplied explicitly. -/
def generatedFourthPairIntegral (s : Fin 2) (i j : Fin 24) : Fin 24 → ℤ := fun k =>
  4 * (if k = i then 1 else 0) + (if s = 0 then -4 else 4) * (if k = j then 1 else 0)

set_option maxHeartbeats 12000000 in
-- Exhaust the two signs and the increasing pairs using exact integer arithmetic.
/-- Exactly one actual preferred pair line pulls back into the selected octad plane. -/
theorem generatedFourth_pair_support_certificate :
    ∀ s : Fin 2, ∀ i j : Fin 24, i < j →
      ((∀ k : Fin 24, Nat.testBit 0xcccc00 k.val = false →
          (generatedFourthInverseNumerator *ᵥ generatedFourthPairIntegral s i j) k = 0) ↔
        s = 1 ∧ i = 8 ∧ j = 11) := by
  decide +kernel

/-- Exact rational inverse matrix in physical coordinates. -/
def generatedFourthInverseMatrixQ : Matrix (Fin 24) (Fin 24) ℚ :=
  generatedFourthInverseNumerator.map (fun z => (z : ℚ) / 4)

set_option maxHeartbeats 12000000 in
-- Check all rational entries after dividing each original Xi numerator by two.
/-- The rational matrix is the actual positive Xi, P0, Xi product. -/
theorem generatedFourth_inverse_matrix_certificate :
    generatedFourthInverseMatrixQ = co1XiMatrixQ *
      generatedFourthPermutationMatrix.map (Int.castRingHom ℚ) * co1XiMatrixQ := by
  decide +kernel

/-- The scaled diagonal of the transported octad projector. -/
def generatedFourthProjectionDiagonal (i : Fin 24) : ℤ :=
  if i = 8 ∨ i = 11 then 10 else if 4 ≤ i.val ∧ i.val < 12 then 2 else 6

set_option maxHeartbeats 12000000 in
-- Only 24 sums of 24 squares are needed for the complete original diagonal.
/-- The original octad projector has the displayed diagonal after local transport. -/
theorem generatedFourth_projection_diagonal_certificate : ∀ i : Fin 24,
    (∑ j : Fin 24, if Nat.testBit 0xcccc00 j.val then
      generatedFourthInverseNumerator j i * generatedFourthInverseNumerator j i else 0) =
        generatedFourthProjectionDiagonal i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

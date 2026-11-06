/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInverseSpatial

/-! Exact rational matrix and signed pair coefficients of the genuine fourth prototype. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Exact rational entries of the actual middle octad projector. -/
def generatedAxisGlobalCanonicalFourthMiddleMatrixQ (i j : Fin 24) : ℚ :=
  (∑ t : Fin 24, if Nat.testBit 0xcccc00 t.val then
    (generatedFourthInverseNumerator t i : ℚ) * (generatedFourthInverseNumerator t j : ℚ)
    else 0) / 16

/-- Every middle real matrix entry equals its explicit rational projector entry. -/
theorem generatedAxisGlobalCanonicalFourthMiddleMatrix_entry (i j : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).1 i j =
      (generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j : ℝ) := by
  rw [generatedFourth_local_matrix, generatedAxis_triality_octad_matrix,
    generatedFourthOctad_mask]
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedFourthLocalFiber.val.2
    (Matrix.diagonal (fun t : Fin 24 => if Nat.testBit 0xcccc00 t.val then 1 else 0))) i j,
    conwayMatrixAction_pairing]
  change Matrix.toBilin' _
    ((generatedFourthLocalFiber⁻¹).val.2.val (Pi.single i 1))
    ((generatedFourthLocalFiber⁻¹).val.2.val (Pi.single j 1)) = _
  rw [generatedFourth_inverse_spatial_action, generatedFourth_inverse_spatial_action]
  simp only [Matrix.mulVec_single, Matrix.toBilin'_apply, Matrix.diagonal_apply,
    MulOpposite.op_one, one_smul, Matrix.col_apply]
  simp_rw [generatedFourth_inverse_matrix_entry]
  rw [generatedAxisGlobalCanonicalFourthMiddleMatrixQ]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hb : Nat.testBit 0xcccc00 t.val = true
  · simp [hb, mul_ite, ite_mul]
    ring
  · simp [hb]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

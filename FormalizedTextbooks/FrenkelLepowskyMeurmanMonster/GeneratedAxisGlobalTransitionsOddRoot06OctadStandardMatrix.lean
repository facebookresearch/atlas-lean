/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadMatrixActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationSpatial

/-! The original seven-letter Mathieu word transports the entire actual projection to the standard octad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 20000000 in
/-- The genuine final coordinate permutation transports exactly the original projection support. -/
theorem generatedAxisGlobalOddRoot06OctadFinal_support : ∀ i : Fin 24,
    (0x714281 : ℕ).testBit (generatedAxisGlobalOddRoot06OctadFinalGolayPermutation.val.symm i).val =
      (0xff00 : ℕ).testBit i.val := by
  decide +kernel

/-- The complete actual outgoing original matrix becomes the standard octad projection. -/
theorem generatedAxisGlobalOddRoot06PositiveStandardProjection_actual :
    conwayMatrixAction generatedAxisGlobalOddRoot06OctadStandardFrameIsometry
      (griessConwayEncode
        (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis))).1 =
      Matrix.diagonal (fun i : Fin 24 =>
        if (0xff00 : ℕ).testBit i.val then (1 : ℝ) else 0) := by
  rw [generatedAxisGlobalOddRoot06OctadStandardFrameIsometry, map_mul]
  change conwayMatrixAction (golayPermutationIsometry generatedAxisGlobalOddRoot06OctadFinalGolayPermutation)
    (conwayMatrixAction generatedAxisGlobalOddRoot06OctadFrameIsometry _) = _
  rw [generatedAxisGlobalOddRoot06PositiveOctadProjection_actual]
  ext i j
  rw [leechRootedA2_permutation_matrix]
  simp only [Matrix.diagonal_apply,
    generatedAxisGlobalOddRoot06OctadFinalGolayPermutation.val.symm.injective.eq_iff,
    generatedAxisGlobalOddRoot06OctadFinal_support]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

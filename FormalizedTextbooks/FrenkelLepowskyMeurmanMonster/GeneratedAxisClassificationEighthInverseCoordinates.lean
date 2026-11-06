/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthSpatial

/-! Integer coordinates of the genuine inverse spatial action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Eight times the genuine inverse real matrix, in standard row convention. -/
def generatedEighthInverseNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  generatedEighthFrameVectorData 7

/-- Every inverse short-vector coordinate has its exact denominator-cleared expression. -/
theorem generatedEighth_inverse_short_coordinate (r : GriessShortIndex) (i : Fin 24) :
    generatedEighthLocalFiber.val.2.val.symm (griessShortVector r) i =
      (((generatedEighthInverseNumerator *ᵥ griessShortIntegral r) i : ℤ) : ℝ) /
        (8 * Real.sqrt 8) := by
  change (generatedEighthLocalFiber.val.2⁻¹).val (griessShortVector r) i = _
  rw [← leechIsomMatrix_mulVec (generatedEighthLocalFiber.val.2⁻¹)]
  change (∑ j, leechIsomMatrix (generatedEighthLocalFiber.val.2⁻¹) i j *
    griessShortVector r j) = _
  simp_rw [generatedEighth_inverse_matrix_coordinate, griessShortVector,
    div_mul_div_comm]
  rw [← Finset.sum_div]
  norm_cast

/-- The original inverse lattice action satisfies the same exact integer equation. -/
theorem generatedEighth_inverse_integral_coordinate (u : leechIntegral) (i : Fin 24) :
    8 * (leechIntegralAction (generatedEighthLocalFiber.val.2⁻¹) u).val i =
      (generatedEighthInverseNumerator *ᵥ u.val) i := by
  have he := congrFun (leechIntegralAction_embedding
    (generatedEighthLocalFiber.val.2⁻¹) u) i
  rw [← leechIsomMatrix_mulVec (generatedEighthLocalFiber.val.2⁻¹)] at he
  change (((leechIntegralAction (generatedEighthLocalFiber.val.2⁻¹) u).val i : ℤ) : ℝ) /
      Real.sqrt 8 = (∑ j, leechIsomMatrix (generatedEighthLocalFiber.val.2⁻¹) i j *
        ((u.val j : ℝ) / Real.sqrt 8)) at he
  simp_rw [generatedEighth_inverse_matrix_coordinate, div_mul_div_comm] at he
  rw [← Finset.sum_div] at he
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hs] at he
  have hi : (leechIntegralAction (generatedEighthLocalFiber.val.2⁻¹) u).val i * 8 =
      ∑ j, generatedEighthFrameVectorData 7 i j * u.val j := by exact_mod_cast he
  simpa only [generatedEighthInverseNumerator, Matrix.mulVec, dotProduct, mul_comm] using hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

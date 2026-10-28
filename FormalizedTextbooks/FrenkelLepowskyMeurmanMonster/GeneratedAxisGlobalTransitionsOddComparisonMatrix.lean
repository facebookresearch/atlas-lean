/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignMatrix

/-! Complete physical matrix constituents of the three genuine phase preserving comparisons. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The comparison matrix includes the actual original Golay coordinate signs. -/
def generatedAxisGlobalOddComparisonMatrixQ (k : Fin 3) :
    Matrix (Fin 24) (Fin 24) ℚ := fun i j =>
  (generatedAxisGlobalIntSign
    ((sourceGeneratedSignCode (generatedAxisGlobalOddComparisonSign k)).val i +
      (sourceGeneratedSignCode (generatedAxisGlobalOddComparisonSign k)).val j) : ℚ) *
    generatedAxisGlobalOddRootMatrixQ (generatedAxisGlobalOddComparisonRoot k) i j

/-- The entire actual comparison matrix agrees with the explicit original rational packet. -/
theorem generatedAxisGlobalOddComparisonMatrix_actual (k : Fin 3) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis)).1 =
      (generatedAxisGlobalOddComparisonMatrixQ k).map (Rat.castHom ℝ) := by
  rw [generatedAxisGlobalOddComparisonLocal, map_mul, map_mul,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  change (griessConwayEncode
    (rhoLocal (localFiberIntoH (localFiberIncl (generatedAxisGlobalOddComparisonQ k)))
      (rhoLocal (generatedFifthSignLocal (generatedAxisGlobalOddComparisonSign k) 0)
        (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
          (generatedAxisGlobalOddComparisonRoot k)) generatedOddAxis)))).1 = _
  rw [generatedFourth_local_matrix]
  change conwayMatrixAction 1 _ = _
  rw [map_one, LinearEquiv.coe_one, id_eq]
  rw [generatedFifth_sign_local_action, sourceGeneratedY_matrix]
  ext i j
  rw [sourceGeneratedSign_matrix_apply, generatedAxisGlobalOddRootMatrix_actual]
  change qSign _ * (generatedAxisGlobalOddRootMatrixQ
    (generatedAxisGlobalOddComparisonRoot k) i j : ℝ) =
      ((generatedAxisGlobalOddComparisonMatrixQ k i j : ℚ) : ℝ)
  simp only [generatedAxisGlobalOddComparisonMatrixQ, Rat.cast_mul, Rat.cast_intCast,
    generatedAxisGlobalIntSign_real]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

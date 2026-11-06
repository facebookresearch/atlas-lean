/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonMatrix

/-! Complete original rational matrix transport by every genuine Golay sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Both original diagonal signs act on every full matrix entry. -/
def generatedAxisGlobalRationalSignMatrix (a : Fin 4096)
    (A : Matrix (Fin 24) (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ := fun i j =>
  (generatedAxisGlobalIntSign ((sourceGeneratedSignCode a).val i) : ℚ) *
    (generatedAxisGlobalIntSign ((sourceGeneratedSignCode a).val j) : ℚ) * A i j

/-- This complete rational matrix action is the actual original local sign action. -/
theorem generatedAxisGlobalRationalSignMatrix_actual (a : Fin 4096)
    (x : GriessSpace) (A : Matrix (Fin 24) (Fin 24) ℚ)
    (hx : (griessConwayEncode x).1 = A.map (Rat.castHom ℝ)) :
    (griessConwayEncode (rhoLocal (generatedFifthSignLocal a 0) x)).1 =
      (generatedAxisGlobalRationalSignMatrix a A).map (Rat.castHom ℝ) := by
  rw [generatedFifth_sign_local_action, sourceGeneratedY_matrix]
  ext i j
  rw [sourceGeneratedSign_matrix_apply, hx]
  change qSign ((sourceGeneratedSignCode a).val i + (sourceGeneratedSignCode a).val j) *
      (A i j : ℝ) = ((generatedAxisGlobalRationalSignMatrix a A i j : ℚ) : ℝ)
  simp only [generatedAxisGlobalRationalSignMatrix, Rat.cast_mul, Rat.cast_intCast,
    generatedAxisGlobalIntSign_real, qSign_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

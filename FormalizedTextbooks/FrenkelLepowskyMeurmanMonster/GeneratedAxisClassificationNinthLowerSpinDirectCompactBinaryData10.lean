/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryMatrix

/-! Complete original binary columns of the oriented compact lift 10. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Compare two single matrix products to avoid repeating nested coordinate changes.
private theorem integral_intertwining :
    generatedNinthLowerSpinDirectIntegralMatrix10.map (Int.castRingHom (ZMod 2)) *
      leechHyperbolicMatrix =
      leechHyperbolicMatrix * generatedNinthLowerSpinDirectCompactBinaryMatrix 10 := by
  decide +kernel

/-- The complete genuine change of lattice basis gives the retained corrected binary matrix. -/
theorem generatedNinth_lower_spin_direct_compact_binary_matrix_10 :
    leechHyperbolicInverse *
      generatedNinthLowerSpinDirectIntegralMatrix10.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix = generatedNinthLowerSpinDirectCompactBinaryMatrix 10 := by
  rw [Matrix.mul_assoc, integral_intertwining, ← Matrix.mul_assoc,
    leechHyperbolicMatrix_inverse.2, Matrix.one_mul]

/-- All twenty-four original columns agree, including their original coordinate basis. -/
theorem generatedNinth_lower_spin_direct_compact_binary_certificate_10 :
    ∀ j : Fin 24,
      toAdd (qQuotHom (generatedNinthLowerSpinCorrection 10 *
        generatedNinthLowerSpinQImage 10 j *
          (generatedNinthLowerSpinCorrection 10)⁻¹)) =
      (leechHyperbolicInverse *
        generatedNinthLowerSpinDirectIntegralMatrix10.map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix) *ᵥ Pi.single j 1 := by
  intro j
  rw [generatedNinth_lower_spin_direct_compact_binary_matrix_10]
  rw [Matrix.mulVec_single_one]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryMatrix

/-! Complete original binary columns of the oriented compact lift 7. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Compare two single matrix products to avoid repeating nested coordinate changes.
private theorem integral_intertwining :
    generatedNinthLowerSpinDirectIntegralMatrix07.map (Int.castRingHom (ZMod 2)) *
      leechHyperbolicMatrix =
      leechHyperbolicMatrix * generatedNinthLowerSpinDirectCompactBinaryMatrix 7 := by
  decide +kernel

/-- The complete genuine change of lattice basis gives the retained corrected binary matrix. -/
theorem generatedNinth_lower_spin_direct_compact_binary_matrix_07 :
    leechHyperbolicInverse *
      generatedNinthLowerSpinDirectIntegralMatrix07.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix = generatedNinthLowerSpinDirectCompactBinaryMatrix 7 := by
  rw [Matrix.mul_assoc, integral_intertwining, ← Matrix.mul_assoc,
    leechHyperbolicMatrix_inverse.2, Matrix.one_mul]

/-- All twenty-four original columns agree, including their original coordinate basis. -/
theorem generatedNinth_lower_spin_direct_compact_binary_certificate_07 :
    ∀ j : Fin 24,
      toAdd (qQuotHom (generatedNinthLowerSpinCorrection 7 *
        generatedNinthLowerSpinQImage 7 j *
          (generatedNinthLowerSpinCorrection 7)⁻¹)) =
      (leechHyperbolicInverse *
        generatedNinthLowerSpinDirectIntegralMatrix07.map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix) *ᵥ Pi.single j 1 := by
  intro j
  rw [generatedNinth_lower_spin_direct_compact_binary_matrix_07]
  rw [Matrix.mulVec_single_one]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

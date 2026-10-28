/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinIntegerModel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedGenerators

/-! The entire genuine inverse-C, Xi, C spin operator has an exact sixty-four-term numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Full original conjugated-Xi numerator with both source-word quadratic phases retained. -/
def generatedSixthXiSpinInteger (v : NortonUIntegerVector) : NortonUIntegerVector :=
  generatedSixthSpinIntegerModel (generatedSixthPermutationProfileInverseModel 1)
    (nortonUIntegerXi
      (generatedSixthSpinIntegerModel (generatedSixthPermutationProfileModel 1) v))

/-- Dividing the original integer numerator by eight gives the actual unmodified raw spin action. -/
theorem generatedSixth_xi_spin_integer_embed (v : NortonUIntegerVector) :
    (generatedSixthRawGenerator 4).val.1.val (nortonUIntegerEmbed v) =
      (1 / 8 : ℝ) • nortonUIntegerEmbed (generatedSixthXiSpinInteger v) := by
  let C := leechRootedA2SixthXiTransportFiber
  have hC := generatedSixth_permutation_profile_spin 1
  change representativeSpinCertificate C.val.1
    (generatedSixthPermutationProfileModel 1).coordinate
    (generatedSixthPermutationProfileModel 1).phase at hC
  have hCi := generatedSixth_permutation_profile_inverse_spin 1
  change representativeSpinCertificate C.val.1⁻¹
    (generatedSixthPermutationProfileInverseModel 1).coordinate
    (generatedSixthPermutationProfileInverseModel 1).phase at hCi
  change C.val.1⁻¹.val (xiSpinHolomorph.val (C.val.1.val (nortonUIntegerEmbed v))) = _
  rw [generatedSixth_spin_integer_model_embed _ _ hC, nortonUIntegerXi_embed, map_smul,
    generatedSixth_spin_integer_model_embed _ _ hCi]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

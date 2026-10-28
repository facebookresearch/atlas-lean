/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectMatrixFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeTensorFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSupportActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeShortSupportCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLocalSpatialProjection

/-! Actual whole-axis fixation and genuine local stabilizer membership from complete source
caches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All three actual coordinate constituents are fixed once their source caches are identified. -/
theorem generatedNinth_lower_spin_three_axis_fix_of_source_caches (g : Fin 3)
    (hspatial : ∀ j k, (generatedNinthLowerSpinTensorSpatialDenominator
      (generatedNinthLowerSpinThreeCandidateIndex g) : ℝ) *
      (generatedNinthLowerSpinDirectIsometry (generatedNinthLowerSpinThreeCandidateIndex
        g)).val (Pi.single k 1) j =
        (generatedNinthLowerSpinTensorSpatialNumerator
          (generatedNinthLowerSpinThreeCandidateIndex g) j k : ℝ))
    (htensor : ∀ t j, 64 * Real.sqrt 2 * (griessConwayEncode generatedNinthAxis).2.2 t j =
      (generatedNinthLowerSpinTensorInputInteger (nortonUIntegerLabel t) j : ℝ))
    (hshort : ∀ r, 256 * (griessConwayEncode generatedNinthAxis).2.1 r =
      (generatedNinthLowerSpinShortInputInteger r : ℝ)) :
    localGriessRepresentation (generatedNinthLowerSpinDirectFiber
      (generatedNinthLowerSpinThreeCandidateIndex g)) generatedNinthAxis =
      generatedNinthAxis := by
  have hmatrix := generatedNinth_lower_spin_direct_matrix_fix_of_source_cache
    (generatedNinthLowerSpinThreeCandidateIndex g) hspatial
  have hS := generatedNinth_lower_spin_direct_short_fix_of_support_cache
    (generatedNinthLowerSpinThreeCandidateIndex g)
    (generatedNinth_lower_spin_three_short_support_certificates g)
    (griessConwayEncode generatedNinthAxis).2.1 hshort
  have hT := generatedNinth_lower_spin_three_tensor_fix_of_source_caches g
    (griessConwayEncode generatedNinthAxis).2.2 htensor hspatial
  have he : griessConwayEncode
      (localGriessRepresentation (generatedNinthLowerSpinDirectFiber
        (generatedNinthLowerSpinThreeCandidateIndex g)) generatedNinthAxis) =
        griessConwayEncode generatedNinthAxis := by
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change (localMatrixRepresentation (generatedNinthLowerSpinDirectFiber
      (generatedNinthLowerSpinThreeCandidateIndex g))
      (griessConwayEncode generatedNinthAxis).1,
        (localShortRepresentation (generatedNinthLowerSpinDirectFiber
          (generatedNinthLowerSpinThreeCandidateIndex g))
          (griessConwayEncode generatedNinthAxis).2.1,
          localTensorRepresentation (generatedNinthLowerSpinDirectFiber
            (generatedNinthLowerSpinThreeCandidateIndex g))
            (griessConwayEncode generatedNinthAxis).2.2)) = _
    rw [hmatrix, hS, hT]
  have hd := congrArg griessConwayDecode he
  simpa only [griessConwayDecode_encode] using hd

/-- The compact fiber is a concrete element of the actual full local Ninth axis stabilizer. -/
theorem generatedNinth_lower_spin_three_axis_local_membership (g : Fin 3)
    (hspatial : ∀ j k, (generatedNinthLowerSpinTensorSpatialDenominator
      (generatedNinthLowerSpinThreeCandidateIndex g) : ℝ) *
      (generatedNinthLowerSpinDirectIsometry (generatedNinthLowerSpinThreeCandidateIndex
        g)).val (Pi.single k 1) j =
        (generatedNinthLowerSpinTensorSpatialNumerator
          (generatedNinthLowerSpinThreeCandidateIndex g) j k : ℝ))
    (htensor : ∀ t j, 64 * Real.sqrt 2 * (griessConwayEncode generatedNinthAxis).2.2 t j =
      (generatedNinthLowerSpinTensorInputInteger (nortonUIntegerLabel t) j : ℝ))
    (hshort : ∀ r, 256 * (griessConwayEncode generatedNinthAxis).2.1 r =
      (generatedNinthLowerSpinShortInputInteger r : ℝ)) :
    generatedNinthLowerSpinDirectLocal (generatedNinthLowerSpinThreeCandidateIndex g) ∈
      generatedNinthLocalAxisStabilizer := by
  change rhoLocal (generatedNinthLowerSpinDirectLocal
    (generatedNinthLowerSpinThreeCandidateIndex g)) generatedNinthAxis = generatedNinthAxis
  exact generatedNinth_lower_spin_three_axis_fix_of_source_caches g hspatial htensor hshort

/-- Actual complete source bindings put the exact original Conway projection in the axis image. -/
theorem generatedNinth_lower_spin_three_axis_projected_membership (g : Fin 3)
    (hspatial : ∀ j k, (generatedNinthLowerSpinTensorSpatialDenominator
      (generatedNinthLowerSpinThreeCandidateIndex g) : ℝ) *
      (generatedNinthLowerSpinDirectIsometry (generatedNinthLowerSpinThreeCandidateIndex
        g)).val (Pi.single k 1) j =
        (generatedNinthLowerSpinTensorSpatialNumerator
          (generatedNinthLowerSpinThreeCandidateIndex g) j k : ℝ))
    (htensor : ∀ t j, 64 * Real.sqrt 2 * (griessConwayEncode generatedNinthAxis).2.2 t j =
      (generatedNinthLowerSpinTensorInputInteger (nortonUIntegerLabel t) j : ℝ))
    (hshort : ∀ r, 256 * (griessConwayEncode generatedNinthAxis).2.1 r =
      (generatedNinthLowerSpinShortInputInteger r : ℝ)) :
    (QuotientGroup.mk (generatedNinthLowerSpinDirectIsometry
      (generatedNinthLowerSpinThreeCandidateIndex g)) : Co1) ∈
      generatedNinthProjectedAxisStabilizer := by
  refine ⟨⟨generatedNinthLowerSpinDirectLocal (generatedNinthLowerSpinThreeCandidateIndex g),
    generatedNinth_lower_spin_three_axis_local_membership g hspatial htensor hshort⟩, ?_⟩
  exact generatedNinth_lower_spin_direct_projection (generatedNinthLowerSpinThreeCandidateIndex g)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

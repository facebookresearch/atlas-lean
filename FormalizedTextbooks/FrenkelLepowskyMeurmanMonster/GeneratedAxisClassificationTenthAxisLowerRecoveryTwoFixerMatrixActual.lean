/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharP.Two

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorCircuitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySmallSourceData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! Ungated genuine matrix fixation for the literal joint9*1 and original10 fibers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem add_self_two (c : ZMod 2) : c + c = 0 :=
  CharTwo.add_self_eq_zero c

/-- The actual identity flag permutation has zero full outside sign correction. -/
theorem generatedTenth_two_fixer_identity_flag_phase :
    generatedTenthE7SignedFlagPhase (1 : generatedTenthE7StandardFlagPermutationGroup) = 0 := by
  have hinj : Function.Injective generatedTenthE7StandardOutsideCoordinates := by
    intro i j h
    apply generatedTenth_e7_standard_outside_point_bijective.1
    apply Subtype.ext
    exact h
  have hone : (1 : generatedTenthE7StandardFlagPermutationGroup).val.val.val =
      Equiv.refl (Fin 24) := rfl
  have he : generatedTenthE7StandardOutsidePermutation
      (1 : generatedTenthE7StandardFlagPermutationGroup) = Equiv.refl (Fin 6) := by
    apply Equiv.ext
    intro i
    change generatedTenthE7StandardOutsidePermutation
      (1 : generatedTenthE7StandardFlagPermutationGroup) i = i
    apply hinj
    simpa only [hone, Equiv.refl_apply] using
      generatedTenth_e7_standard_outside_permutation_coordinate
        (1 : generatedTenthE7StandardFlagPermutationGroup) i
  funext i
  change generatedTenthE7StandardOutsideSigns i + generatedTenthE7StandardOutsideSigns
    ((generatedTenthE7StandardOutsidePermutation
      (1 : generatedTenthE7StandardFlagPermutationGroup)).symm i) = 0
  rw [he]
  simp only [Equiv.refl_symm, Equiv.refl_apply]
  exact add_self_two _

/-- The literal original code11 is a true identity-permutation signed flag candidate. -/
def generatedTenthTwoFixerSignElevenCandidate : generatedTenthE7SignedFlagCandidates :=
  ⟨1, ⟨generatedTenthAxisLowerRecoveryCode 11, by
    rw [generatedTenth_two_fixer_identity_flag_phase]
    simpa [generatedTenthAxisLowerRecoverySignBasis] using
      generatedTenth_axis_lower_recovery_sign_basis_valid (1 : Fin 7)⟩⟩

/-- The complete genuine candidate has exactly the original spatial sign11 action. -/
theorem generatedTenth_two_fixer_sign_eleven_candidate_spatial :
    generatedTenthE7SignedFlagSpatial generatedTenthTwoFixerSignElevenCandidate =
      golaySignIsometry (generatedTenthAxisLowerRecoveryCode 11) := by
  change golaySignIsometry (generatedTenthAxisLowerRecoveryCode 11) *
    golayPermutationIsometry 1 = _
  rw [show golayPermutationIsometry 1 = 1 from golayPermutationHom.map_one, mul_one]

/-- The whole actual anchor enumeration supplies genuine full standard matrix membership. -/
theorem generatedTenth_two_fixer_sign_eleven_standard_mem :
    golaySignIsometry (generatedTenthAxisLowerRecoveryCode 11) ∈
      generatedTenthE7StandardMatrixGroup := by
  have h := (generatedTenthE7SignedAnchorEnumeration
    generatedTenthTwoFixerSignElevenCandidate).val.property
  change generatedTenthE7SignedFlagSpatial generatedTenthTwoFixerSignElevenCandidate ∈
    generatedTenthE7StandardMatrixGroup at h
  rwa [generatedTenth_two_fixer_sign_eleven_candidate_spatial] at h

/-- Source1 is exactly the actual signed anchor, transported into original matrix coordinates. -/
theorem generatedTenth_two_fixer_original_one_mem :
    generatedTenthAxisLowerRecoveryCompactSpatial 1 ∈ generatedTenthE7OriginalMatrixGroup := by
  change generatedTenthAxisLowerRecoveryCompactStandardSpatial 1 ∈
    generatedTenthE7StandardMatrixGroup
  simpa [generatedTenthAxisLowerRecoveryCompactStandardSpatial,
    generatedTenthAxisLowerRecoverySignBasis] using
    generatedTenth_two_fixer_sign_eleven_standard_mem

/-- Source9 is the first frozen genuine root-orbit letter in original matrix coordinates. -/
theorem generatedTenth_two_fixer_original_nine_mem :
    generatedTenthAxisLowerRecoveryCompactSpatial 9 ∈ generatedTenthE7OriginalMatrixGroup := by
  change generatedTenthAxisLowerRecoveryCompactStandardSpatial 9 ∈
    generatedTenthE7StandardMatrixGroup
  simpa [generatedTenthAxisLowerRecoveryCompactStandardSpatial] using
    generatedTenth_e7_orbit_letter_mem (0 : Fin 2)

/-- Source10 is the second frozen genuine root-orbit letter in original matrix coordinates. -/
theorem generatedTenth_two_fixer_original_ten_mem :
    generatedTenthAxisLowerRecoveryCompactSpatial 10 ∈ generatedTenthE7OriginalMatrixGroup := by
  change generatedTenthAxisLowerRecoveryCompactStandardSpatial 10 ∈
    generatedTenthE7StandardMatrixGroup
  simpa [generatedTenthAxisLowerRecoveryCompactStandardSpatial] using
    generatedTenth_e7_orbit_letter_mem (1 : Fin 2)

/-- Both compatible fibers have their literal spatial value in the entire actual matrix group. -/
theorem generatedTenth_two_fixer_matrix_group_mem (g : Fin 2) :
    (generatedTenthTwoFixerTensorFiber g).val.2 ∈ generatedTenthE7OriginalMatrixGroup := by
  fin_cases g
  · change generatedTenthTwoFixerJointFiber.val.2 ∈ generatedTenthE7OriginalMatrixGroup
    rw [generatedTenth_two_fixer_joint_spatial]
    exact generatedTenthE7OriginalMatrixGroup.mul_mem
      generatedTenth_two_fixer_original_nine_mem generatedTenth_two_fixer_original_one_mem
  · change generatedTenthAxisLowerRecoveryCompactSpatial 10 ∈ generatedTenthE7OriginalMatrixGroup
    exact generatedTenth_two_fixer_original_ten_mem

/-- Both literal actual fibers fix the entire actual matrix, without a matrix-fixer hypothesis. -/
theorem generatedTenth_two_fixer_matrix_action_fix (g : Fin 2) :
    conwayMatrixAction (generatedTenthTwoFixerTensorFiber g).val.2
      (griessConwayEncode generatedTenthAxis).1 = (griessConwayEncode generatedTenthAxis).1 :=
  generatedTenth_two_fixer_matrix_group_mem g

/-- The actual original Griess action therefore preserves the whole encoded matrix block. -/
theorem generatedTenth_two_fixer_matrix_actual_fix (g : Fin 2) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthAxis)).1 = (griessConwayEncode generatedTenthAxis).1 := by
  rw [generatedFourth_local_matrix]
  exact generatedTenth_two_fixer_matrix_action_fix g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

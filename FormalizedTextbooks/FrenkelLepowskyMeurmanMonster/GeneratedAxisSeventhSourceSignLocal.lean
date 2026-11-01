/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionProjection

/-! The opposite genuine triality conjugates provide local lifts of original Golay signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original code conjugate in the orientation of the seventh axis. -/
def generatedSeventhSourceZ (d : Fin 4096) (ε : ZMod 2) : G :=
  extraIntoGenerated * sourceGeneratedCode d ε * extraIntoGenerated⁻¹

/-- Opposite triality transports the central involution to the actual source Omega element. -/
theorem generatedSeventh_inverse_central :
    extraIntoGenerated⁻¹ * qIntoGenerated qCentralInvolution * extraIntoGenerated =
      qIntoGenerated sourceOmegaQ := by
  rw [qIntoGenerated_sourceOmegaQ]
  apply Subtype.ext
  change sExtra⁻¹ * localCentralGriess * sExtra = trialityCentralSign 2
  have hi : sExtra⁻¹ = sExtra ^ 2 := by
    calc
      _ = sExtra⁻¹ * 1 := by simp
      _ = sExtra⁻¹ * sExtra ^ 3 := by rw [sExtra_pow_three]
      _ = _ := by group
  have h := localCentralGriess_conjugate_square
  rw [← hi] at h
  rw [inv_inv] at h
  exact h

/-- The opposite code conjugate centralizes the genuine central involution before local lifting. -/
theorem generatedSeventhSourceZ_commute_central (d : Fin 4096) (ε : ZMod 2) :
    generatedSeventhSourceZ d ε * qIntoGenerated qCentralInvolution =
      qIntoGenerated qCentralInvolution * generatedSeventhSourceZ d ε := by
  have h := sourceGeneratedCode_commute_sign_two d ε
  rw [← qIntoGenerated_sourceOmegaQ, ← generatedSeventh_inverse_central] at h
  unfold generatedSeventhSourceZ
  calc
    _ = extraIntoGenerated *
        (sourceGeneratedCode d ε * (extraIntoGenerated⁻¹ *
          qIntoGenerated qCentralInvolution * extraIntoGenerated)) * extraIntoGenerated⁻¹ := by
      group
    _ = extraIntoGenerated *
        ((extraIntoGenerated⁻¹ * qIntoGenerated qCentralInvolution * extraIntoGenerated) *
          sourceGeneratedCode d ε) * extraIntoGenerated⁻¹ := by rw [h]
    _ = _ := by group

/-- The proved full centralizer supplies a genuine local lift of the opposite code conjugate. -/
theorem generatedSeventh_source_sign_local_exists (d : Fin 4096) (ε : ZMod 2) :
    ∃ h : H, localIntoGenerated h = generatedSeventhSourceZ d ε := by
  have hm : generatedSeventhSourceZ d ε ∈
      Subgroup.centralizer {qIntoGenerated qCentralInvolution} :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (generatedSeventhSourceZ_commute_central d ε)
  rw [generatedCentralizer_eq_local_range] at hm
  exact hm

/-- An actual local element representing the opposite original code conjugate. -/
def generatedSeventhSourceSignLocal (d : Fin 4096) (ε : ZMod 2) : H :=
  Classical.choose (generatedSeventh_source_sign_local_exists d ε)

/-- The local lift is exactly the original opposite source word in the generated group. -/
theorem generatedSeventh_source_sign_local_generated (d : Fin 4096) (ε : ZMod 2) :
    localIntoGenerated (generatedSeventhSourceSignLocal d ε) = generatedSeventhSourceZ d ε :=
  Classical.choose_spec (generatedSeventh_source_sign_local_exists d ε)

/-- Its action is triality, the genuine original code lift, then inverse triality. -/
theorem generatedSeventh_source_sign_local_apply (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) :
    rhoLocal (generatedSeventhSourceSignLocal d ε) x =
      sExtra (rhoLocal (inclQ (sourceQCode d ε)) (sExtra⁻¹ x)) := by
  have h := congrArg Subtype.val (generatedSeventh_source_sign_local_generated d ε)
  change rhoLocal (generatedSeventhSourceSignLocal d ε) =
    (generatedSeventhSourceZ d ε).val at h
  rw [h]
  rfl

/-- The C row of the original code action has the same physical pair sign as B. -/
theorem generatedSeventh_source_code_blocks_C (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 2 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 2 p := by
  have he := localGriessRepresentation_encode (localFiberIncl (sourceQCode d ε)) x
  have h0 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (0,p))) he
  have h1 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (1,p))) he
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 (Sum.inl (0,p)) =
    localShortRepresentation (localFiberIncl (sourceQCode d ε)) (griessConwayEncode x).2.1
      (Sum.inl (0,p)) at h0
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 (Sum.inl (1,p)) =
    localShortRepresentation (localFiberIncl (sourceQCode d ε)) (griessConwayEncode x).2.1
      (Sum.inl (1,p)) at h1
  rw [sourceQCode_short_pair] at h0 h1
  simp only [griessConwayEncode, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h0 h1
  linarith

/-- Triality takes the A coordinate from the C row. -/
theorem generatedSeventh_extra_blocks_A (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra x)).2.1 0 p = (trialityBlocksEquiv x).2.1 2 p := by
  rw [generatedExtra_blocks]
  change trialityCycleAction 276 (trialityBlocksEquiv x).2.1 0 p = _
  simp only [trialityCycleAction, LinearEquiv.piCongrLeft'_apply]
  rfl

/-- Inverse triality takes the C coordinate from the A row. -/
theorem generatedSeventh_extra_inverse_blocks_C (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra⁻¹ x)).2.1 2 p = (trialityBlocksEquiv x).2.1 0 p := by
  rw [generatedExtra_inverse_blocks]
  change (trialityCycleAction 276).symm (trialityBlocksEquiv x).2.1 2 p = _
  rw [trialityCycleAction_inverse_apply]
  rfl

/-- The original opposite conjugate fixes every diagonal dictionary coordinate. -/
theorem generatedSeventh_source_sign_blocks_diagonal (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) :
    (trialityBlocksEquiv ((generatedSeventhSourceZ d ε).val x)).1 =
      (trialityBlocksEquiv x).1 := by
  change (trialityBlocksEquiv
    (sExtra (rhoLocal (inclQ (sourceQCode d ε)) (sExtra⁻¹ x)))).1 = _
  rw [generatedExtra_blocks_diagonal, sourceQCode_blocks_diagonal,
    generatedExtra_inverse_blocks_diagonal]

/-- The original opposite conjugate scales A by the physical Golay pair character. -/
theorem generatedSeventh_source_sign_blocks_A (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv ((generatedSeventhSourceZ d ε).val x)).2.1 0 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 0 p := by
  change (trialityBlocksEquiv
    (sExtra (rhoLocal (inclQ (sourceQCode d ε)) (sExtra⁻¹ x)))).2.1 0 p = _
  rw [generatedSeventh_extra_blocks_A, generatedSeventh_source_code_blocks_C,
    generatedSeventh_extra_inverse_blocks_C]

/-- Its entire genuine matrix action is the original physical Golay sign isometry. -/
theorem generatedSeventh_source_sign_matrix (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) :
    (griessConwayEncode ((generatedSeventhSourceZ d ε).val x)).1 =
      conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode d))
        (griessConwayEncode x).1 := by
  ext i j
  rw [sourceGeneratedSign_matrix_apply]
  by_cases hij : i = j
  · subst j
    simp only [griessConwayEncode, dite_true, generatedSeventh_source_sign_blocks_diagonal,
      CharTwo.add_self_eq_zero, qSign_zero, one_mul]
  · have hp : golayEncoder (golayLabelCoefficients d)
        (griessCoordinatePair (griessPairIndex i j hij)).1 +
        golayEncoder (golayLabelCoefficients d)
          (griessCoordinatePair (griessPairIndex i j hij)).2 =
        golayEncoder (golayLabelCoefficients d) i + golayEncoder (golayLabelCoefficients d) j := by
      rw [griessPairIndex_coordinates]
      split_ifs
      · rfl
      · exact add_comm _ _
    simp only [griessConwayEncode, hij, dite_false]
    rw [generatedSeventh_source_sign_blocks_A, hp]

/-- The actual Conway projection of the opposite source conjugate is the genuine Golay sign. -/
theorem generatedSeventh_source_sign_local_projection (d : Fin 4096) (ε : ZMod 2) :
    projH (generatedSeventhSourceSignLocal d ε) =
      (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) := by
  apply projH_eq_of_matrix_action
  intro x
  have h := congrArg Subtype.val (generatedSeventh_source_sign_local_generated d ε)
  change rhoLocal (generatedSeventhSourceSignLocal d ε) =
    (generatedSeventhSourceZ d ε).val at h
  rw [h]
  exact generatedSeventh_source_sign_matrix d ε x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

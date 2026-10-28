/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMiddleFrameMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationConjugateMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCosets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalGenerationMatrixKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhProjectionTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignLocal

/-! Every genuine triangle-compatible unsigned permutation has a full-axis fixing projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual triangle-compatible unsigned permutation belongs to the full-axis projection.
The lift is constructed from the canonical extraspecial automorphism, retaining its phases. -/
theorem generatedSeventh_permutation_mem_projected (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) :
    QuotientGroup.mk' signsSubgroup (golayPermutationIsometry p) ∈
      generatedSeventhProjectedAxisStabilizer := by
  obtain ⟨f, hf, hOmega, hphase⟩ := generatedSeventh_permutation_pair_lift p
  have hn : localFiberIntoH f ∈ localOmegaStabilizer :=
    (localOmegaStabilizer_fiber_iff f).mpr hOmega
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_conjugate ⟨localFiberIntoH f, hn⟩
  have hka (x : GriessSpace) : rhoLocal k.val x =
      sExtra (rhoLocal (localFiberIntoH f) (sExtra⁻¹ x)) := by
    have h := congrArg (fun u : G => u.val x) hk
    exact h.symm
  have hkm (x : GriessSpace) : (griessConwayEncode (rhoLocal k.val x)).1 =
      conwayMatrixAction (golayPermutationIsometry p) (griessConwayEncode x).1 := by
    rw [hka]
    exact generatedSeventh_permutation_conjugate_matrix p f hf hphase x
  have hkproj : projH k.val =
      QuotientGroup.mk' signsSubgroup (golayPermutationIsometry p) :=
    projH_eq_of_matrix_action k.val _ hkm
  obtain ⟨d, hd, ha⟩ := generatedSeventh_middle_permutation_sign_label p hp
  let g := generatedFifthSignLocal d 0 * k.val
  let b := generatedSeventhSourceSignLocal d 0 * localFiberIntoH f
  have hy : rhoLocal (generatedFifthSignLocal d 0) = (sourceGeneratedY d 0).val :=
    generatedFifth_sign_local_action d 0
  have hz : rhoLocal (generatedSeventhSourceSignLocal d 0) =
      (generatedSeventhSourceZ d 0).val :=
    congrArg Subtype.val (generatedSeventh_source_sign_local_generated d 0)
  have hword : localIntoGenerated g =
      extraIntoGenerated * localIntoGenerated b * extraIntoGenerated⁻¹ := by
    simp only [g, b, map_mul, generatedFifth_sign_local_generated,
      generatedSeventh_source_sign_local_generated]
    have htwo : extraIntoGenerated * extraIntoGenerated = extraIntoGenerated⁻¹ := by
      have h := congrArg Inv.inv extraIntoGenerated_inv_mul_inv
      simpa only [mul_inv_rev, inv_inv] using h
    unfold generatedSeventhSourceZ
    rw [← hk]
    change (extraIntoGenerated⁻¹ * sourceGeneratedCode d 0 * extraIntoGenerated) *
      (extraIntoGenerated * localIntoGenerated (localFiberIntoH f) * extraIntoGenerated⁻¹) = _
    calc
      _ = extraIntoGenerated⁻¹ * sourceGeneratedCode d 0 *
          (extraIntoGenerated * extraIntoGenerated) *
          localIntoGenerated (localFiberIntoH f) * extraIntoGenerated⁻¹ := by group
      _ = (extraIntoGenerated * extraIntoGenerated) * sourceGeneratedCode d 0 *
          extraIntoGenerated⁻¹ * localIntoGenerated (localFiberIntoH f) *
            extraIntoGenerated⁻¹ := by simp only [htwo]
      _ = _ := by group
  have hb : (griessConwayEncode (rhoLocal b
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis))).1 =
      (griessConwayEncode
        (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1 := by
    simp only [b, map_mul, LinearEquiv.mul_apply]
    rw [hz, generatedSeventh_source_sign_matrix, generatedFourth_local_matrix, hf, hd]
    rw [← LinearEquiv.mul_apply, ← map_mul]
    exact generatedSeventh_middle_permutation_matrix_fixed p hp
  have hg : (griessConwayEncode (rhoLocal g generatedSeventhAxis)).1 =
      (griessConwayEncode generatedSeventhAxis).1 := by
    simp only [g, map_mul, LinearEquiv.mul_apply]
    rw [hy, sourceGeneratedY_matrix, hkm]
    have hpfix := generatedSeventh_triangle_permutation_spatial p hp
    change conwayMatrixAction (golayPermutationIsometry p)
      (griessConwayEncode generatedSeventhAxis).1 = _ at hpfix
    rw [hpfix]
    exact (generatedSeventh_sign_spatial_mem_iff d).mpr
      ((generatedSeventhSignParameter_mem_iff _).mp ha)
  have hproj := generatedSeventh_projected_transport g b hword hb hg
  change projH (generatedFifthSignLocal d 0 * k.val) ∈ _ at hproj
  rw [map_mul, generatedFifth_sign_local_projection, hkproj] at hproj
  have hsign := generatedSeventh_sign_mem_projected d ha
  have h := generatedSeventhProjectedAxisStabilizer.mul_mem
    (generatedSeventhProjectedAxisStabilizer.inv_mem hsign) hproj
  simpa only [inv_mul_cancel_left] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

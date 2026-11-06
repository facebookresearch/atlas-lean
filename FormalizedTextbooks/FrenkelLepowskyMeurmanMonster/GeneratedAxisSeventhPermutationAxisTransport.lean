/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMiddleFrameMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhProjectionTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignLocal

/-! Triangle-compatible permutation lifts fixing actual triality give full-axis projections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine triality-commuting local permutation lift supplies its full-axis projection.
The local lift and its commutation with actual triality are explicit inputs. -/
theorem generatedSeventh_permutation_axis_transport (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) (f : localFiberSubgroup)
    (hf : f.val.2 = golayPermutationIsometry p)
    (ht : Commute (localIntoGenerated (localFiberIntoH f)) extraIntoGenerated) :
    QuotientGroup.mk' signsSubgroup (golayPermutationIsometry p) ∈
      generatedSeventhProjectedAxisStabilizer := by
  obtain ⟨d, hd, ha⟩ := generatedSeventh_middle_permutation_sign_label p hp
  let g := generatedFifthSignLocal d 0 * localFiberIntoH f
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
    have hcomm := ht.inv_right.eq
    unfold generatedSeventhSourceZ
    change (extraIntoGenerated⁻¹ * sourceGeneratedCode d 0 * extraIntoGenerated) *
      localIntoGenerated (localFiberIntoH f) = _
    symm
    calc
      _ = (extraIntoGenerated * extraIntoGenerated) * sourceGeneratedCode d 0 *
          extraIntoGenerated⁻¹ *
            (localIntoGenerated (localFiberIntoH f) * extraIntoGenerated⁻¹) := by group
      _ = (extraIntoGenerated * extraIntoGenerated) * sourceGeneratedCode d 0 *
          extraIntoGenerated⁻¹ *
            (extraIntoGenerated⁻¹ * localIntoGenerated (localFiberIntoH f)) := by rw [hcomm]
      _ = (extraIntoGenerated * extraIntoGenerated) * sourceGeneratedCode d 0 *
          (extraIntoGenerated⁻¹ * extraIntoGenerated⁻¹) *
            localIntoGenerated (localFiberIntoH f) := by group
      _ = _ := by rw [htwo, extraIntoGenerated_inv_mul_inv]
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
    rw [hy, sourceGeneratedY_matrix, generatedFourth_local_matrix, hf]
    have hpfix := generatedSeventh_triangle_permutation_spatial p hp
    change conwayMatrixAction (golayPermutationIsometry p)
      (griessConwayEncode generatedSeventhAxis).1 = _ at hpfix
    rw [hpfix]
    exact (generatedSeventh_sign_spatial_mem_iff d).mpr
      ((generatedSeventhSignParameter_mem_iff _).mp ha)
  have hproj := generatedSeventh_projected_transport g b hword hb hg
  have hfproj : projH (localFiberIntoH f) =
      QuotientGroup.mk' signsSubgroup (golayPermutationIsometry p) := by
    change QuotientGroup.mk' signsSubgroup f.val.2 = _
    rw [hf]
  change projH (generatedFifthSignLocal d 0 * localFiberIntoH f) ∈ _ at hproj
  rw [map_mul, generatedFifth_sign_local_projection, hfproj] at hproj
  have hsign := generatedSeventh_sign_mem_projected d ha
  have h := generatedSeventhProjectedAxisStabilizer.mul_mem
    (generatedSeventhProjectedAxisStabilizer.inv_mem hsign) hproj
  simpa only [inv_mul_cancel_left] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

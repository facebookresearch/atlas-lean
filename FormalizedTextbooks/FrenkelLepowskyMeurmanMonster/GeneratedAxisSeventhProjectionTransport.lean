/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMiddleMatrixFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhEvenPauliLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignProjectionCount

/-! A genuine two-frame matrix contract suffices for a full-axis projected lift. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A local candidate whose opposite triality conjugate is local and fixes the actual middle
matrix has a full-axis projection, provided it also fixes the actual final matrix.
All three hypotheses concern the original local operators; no binary-only substitute is used. -/
theorem generatedSeventh_projected_transport (g b : H)
    (hg : localIntoGenerated g =
      extraIntoGenerated * localIntoGenerated b * extraIntoGenerated⁻¹)
    (hm : (griessConwayEncode (rhoLocal b
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis))).1 =
        (griessConwayEncode
          (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1)
    (hf : (griessConwayEncode (rhoLocal g generatedSeventhAxis)).1 =
      (griessConwayEncode generatedSeventhAxis).1) :
    projH g ∈ generatedSeventhProjectedAxisStabilizer := by
  obtain ⟨q, hq, hfixq⟩ := generatedSeventh_middle_matrix_even_phase b hm
  obtain ⟨d, _, k, hk, hp, hmatrix⟩ := generatedSeventh_even_pauli_local_matrix q hq
  have hgval : rhoLocal g = sExtra * rhoLocal b * sExtra⁻¹ := congrArg Subtype.val hg
  have hkval : rhoLocal k = sExtra * rhoLocal (inclQ q) * sExtra⁻¹ :=
    congrArg Subtype.val hk
  have hfix : rhoLocal (k * g) generatedSeventhAxis = generatedSeventhAxis := by
    rw [map_mul, LinearEquiv.mul_apply, hkval, hgval, generatedSeventhAxis_local_expression]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    rw [hfixq]
  have hdmat : golaySignIsometry (sourceGeneratedSignCode d) ∈
      generatedSeventhSpatialStabilizer := by
    have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hfix
    rw [map_mul, LinearEquiv.mul_apply, hmatrix, hf] at h
    exact h
  have hd : golayLabelCoefficients d ∈ generatedSeventhSignParameterSpace :=
    (generatedSeventhSignParameter_mem_iff _).mpr
      ((generatedSeventh_sign_spatial_mem_iff d).mp hdmat)
  have hkg : projH (k * g) ∈ generatedSeventhProjectedAxisStabilizer := ⟨⟨k * g, hfix⟩, rfl⟩
  rw [map_mul, hp] at hkg
  have hkproj := generatedSeventh_sign_mem_projected d hd
  have h := generatedSeventhProjectedAxisStabilizer.mul_mem
    (generatedSeventhProjectedAxisStabilizer.inv_mem hkproj) hkg
  simpa only [inv_mul_cancel_left] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

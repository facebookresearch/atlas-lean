/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhFrameData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhVector

/-! Exact transport of every physical coordinate frame under the original spatial word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

private theorem permutation_step (k : Fin 2) (u : leechIntegral) (v w : Fin 24 → ℤ)
    (hu : u.val = v) (hw : w = golayIntegerPermute (omegaOrbitPermutation k) v) :
    (leechIntegralAction (omegaOrbitPermutationIsometry k) u).val = w := by
  change (leechIntegralAction (golayPermutationIsometry (omegaOrbitGolayPermutation k)) u).val = w
  rw [leechIntegralAction_golayPermutation, hu]
  exact hw.symm

private theorem xi_step (u : leechIntegral) (v w : Fin 24 → ℤ)
    (hu : u.val = v) (hw : (2 : ℕ) • w = co1XiNumerator *ᵥ v) :
    (leechIntegralAction co1XiIsometry u).val = w := by
  have h := co1Xi_integral_double u
  rw [hu, ← hw] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, nsmul_eq_mul] at hi
  omega

/-- Every genuine coordinate-frame vector has its certified original spatial image. -/
theorem generatedSeventh_frame_vector_action (j : Fin 24) :
    (leechIntegralAction generatedSeventhLocalFiber.val.2 (leechCoordinateFrameLattice j)).val =
      generatedSeventhFrameVectorData 7 j := by
  rcases generatedSeventh_frame_vector_certificate j with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  let u0 := leechCoordinateFrameLattice j
  let u1 := leechIntegralAction co1XiIsometry u0
  let u2 := leechIntegralAction (omegaOrbitPermutationIsometry 0) u1
  let u3 := leechIntegralAction (omegaOrbitPermutationIsometry 1) u2
  let u4 := leechIntegralAction (omegaOrbitPermutationIsometry 0) u3
  let u5 := leechIntegralAction co1XiIsometry u4
  let u6 := leechIntegralAction (omegaOrbitPermutationIsometry 1) u5
  let u7 := leechIntegralAction co1XiIsometry u6
  have hv0 : u0.val = generatedSeventhFrameVectorData 0 j := h0.symm
  have hv1 : u1.val = generatedSeventhFrameVectorData 1 j :=
    xi_step u0 _ _ hv0 h1
  have hv2 : u2.val = generatedSeventhFrameVectorData 2 j :=
    permutation_step 0 u1 _ _ hv1 h2
  have hv3 : u3.val = generatedSeventhFrameVectorData 3 j :=
    permutation_step 1 u2 _ _ hv2 h3
  have hv4 : u4.val = generatedSeventhFrameVectorData 4 j :=
    permutation_step 0 u3 _ _ hv3 h4
  have hv5 : u5.val = generatedSeventhFrameVectorData 5 j :=
    xi_step u4 _ _ hv4 h5
  have hv6 : u6.val = generatedSeventhFrameVectorData 6 j :=
    permutation_step 1 u5 _ _ hv5 h6
  have hv7 : u7.val = generatedSeventhFrameVectorData 7 j :=
    xi_step u6 _ _ hv6 h7
  rw [generatedSeventh_local_spatial]
  simpa only [map_mul, LinearEquiv.mul_apply] using hv7


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

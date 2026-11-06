/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthVectorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderNormEightOrbit

/-! The integer vector certificates are transported to the original lattice action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
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

/-- The literal original local fiber has precisely the displayed eight spatial factors. -/
theorem generatedSixth_local_spatial :
    generatedSixthLocalFiber.val.2 = co1XiIsometry * omegaOrbitPermutationIsometry 1 *
      co1XiIsometry * omegaOrbitPermutationIsometry 0 * omegaOrbitPermutationIsometry 1 *
      omegaOrbitPermutationIsometry 0 * co1XiIsometry * omegaOrbitPermutationIsometry 0 := by
  rfl

/-- The original spatial word maps the genuine coordinate frame vector to the certified vector. -/
theorem generatedSixth_normEight_vector_action :
    (leechIntegralAction generatedSixthLocalFiber.val.2 leechNormEightAxis.val).val =
      generatedSixthNormEightVectorData 8 := by
  rcases generatedSixth_normEight_vector_certificate with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  let u0 := leechNormEightAxis.val
  let u1 := leechIntegralAction (omegaOrbitPermutationIsometry 0) u0
  let u2 := leechIntegralAction co1XiIsometry u1
  let u3 := leechIntegralAction (omegaOrbitPermutationIsometry 0) u2
  let u4 := leechIntegralAction (omegaOrbitPermutationIsometry 1) u3
  let u5 := leechIntegralAction (omegaOrbitPermutationIsometry 0) u4
  let u6 := leechIntegralAction co1XiIsometry u5
  let u7 := leechIntegralAction (omegaOrbitPermutationIsometry 1) u6
  let u8 := leechIntegralAction co1XiIsometry u7
  have hv0 : u0.val = generatedSixthNormEightVectorData 0 := by
    funext i
    fin_cases i <;> rfl
  have hv1 : u1.val = generatedSixthNormEightVectorData 1 := permutation_step 0 u0 _ _ hv0 h1
  have hv2 : u2.val = generatedSixthNormEightVectorData 2 := xi_step u1 _ _ hv1 h2
  have hv3 : u3.val = generatedSixthNormEightVectorData 3 := permutation_step 0 u2 _ _ hv2 h3
  have hv4 : u4.val = generatedSixthNormEightVectorData 4 := permutation_step 1 u3 _ _ hv3 h4
  have hv5 : u5.val = generatedSixthNormEightVectorData 5 := permutation_step 0 u4 _ _ hv4 h5
  have hv6 : u6.val = generatedSixthNormEightVectorData 6 := xi_step u5 _ _ hv5 h6
  have hv7 : u7.val = generatedSixthNormEightVectorData 7 := permutation_step 1 u6 _ _ hv6 h7
  have hv8 : u8.val = generatedSixthNormEightVectorData 8 := xi_step u7 _ _ hv7 h8
  rw [generatedSixth_local_spatial]
  simpa only [map_mul, LinearEquiv.mul_apply] using hv8

/-- The actual spatial image, as a genuine norm-eight lattice vector. -/
def generatedSixthNormEightVector : LeechNormEight :=
  ⟨leechIntegralAction generatedSixthLocalFiber.val.2 leechNormEightAxis.val, by
    rw [leechIntegralAction_squareSum]
    exact leechNormEightAxis.property⟩

/-- The genuine norm-eight vector has exactly the checked physical integer coordinates. -/
theorem generatedSixthNormEightVector_val :
    generatedSixthNormEightVector.val.val = generatedSixthNormEightVectorData 8 :=
  generatedSixth_normEight_vector_action

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

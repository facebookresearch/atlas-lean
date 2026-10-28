/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhVectorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderNormEightOrbit

/-! The seventh prototype's spatial frame image in the actual Leech lattice. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

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

/-- The full original fiber has exactly the seven spatial factors used in the integer
    certificates. -/
theorem generatedSeventh_local_spatial :
    generatedSeventhLocalFiber.val.2 = co1XiIsometry * omegaOrbitPermutationIsometry 1 *
      co1XiIsometry * omegaOrbitPermutationIsometry 0 * omegaOrbitPermutationIsometry 1 *
      omegaOrbitPermutationIsometry 0 * co1XiIsometry := by
  rfl

/-- The actual spatial action maps the positive frame vector to the certified integer vector. -/
theorem generatedSeventh_normEight_vector_action :
    (leechIntegralAction generatedSeventhLocalFiber.val.2 leechNormEightAxis.val).val =
      generatedSeventhNormEightVectorData 7 := by
  rcases generatedSeventh_normEight_vector_certificate with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  let u0 := leechNormEightAxis.val
  let u1 := leechIntegralAction co1XiIsometry u0
  let u2 := leechIntegralAction (omegaOrbitPermutationIsometry 0) u1
  let u3 := leechIntegralAction (omegaOrbitPermutationIsometry 1) u2
  let u4 := leechIntegralAction (omegaOrbitPermutationIsometry 0) u3
  let u5 := leechIntegralAction co1XiIsometry u4
  let u6 := leechIntegralAction (omegaOrbitPermutationIsometry 1) u5
  let u7 := leechIntegralAction co1XiIsometry u6
  have hv0 : u0.val = generatedSeventhNormEightVectorData 0 := by
    funext i
    fin_cases i <;> rfl
  have hv1 : u1.val = generatedSeventhNormEightVectorData 1 := xi_step u0 _ _ hv0 h1
  have hv2 : u2.val = generatedSeventhNormEightVectorData 2 := permutation_step 0 u1 _ _ hv1 h2
  have hv3 : u3.val = generatedSeventhNormEightVectorData 3 := permutation_step 1 u2 _ _ hv2 h3
  have hv4 : u4.val = generatedSeventhNormEightVectorData 4 := permutation_step 0 u3 _ _ hv3 h4
  have hv5 : u5.val = generatedSeventhNormEightVectorData 5 := xi_step u4 _ _ hv4 h5
  have hv6 : u6.val = generatedSeventhNormEightVectorData 6 := permutation_step 1 u5 _ _ hv5 h6
  have hv7 : u7.val = generatedSeventhNormEightVectorData 7 := xi_step u6 _ _ hv6 h7
  rw [generatedSeventh_local_spatial]
  simpa only [map_mul, LinearEquiv.mul_apply] using hv7

/-- The spatially transported frame vector is a genuine norm-eight lattice vector. -/
def generatedSeventhNormEightVector : LeechNormEight :=
  ⟨leechIntegralAction generatedSeventhLocalFiber.val.2 leechNormEightAxis.val, by
    rw [leechIntegralAction_squareSum]
    exact leechNormEightAxis.property⟩

/-- The genuine frame image has the original certified physical coordinates. -/
theorem generatedSeventhNormEightVector_val :
    generatedSeventhNormEightVector.val.val = generatedSeventhNormEightVectorData 7 :=
  generatedSeventh_normEight_vector_action

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

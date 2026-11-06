/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQMiddleNormalizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthMonomialMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProduct

/-! Forward triality transport retains the original coordinate permutation on diagonal matrices. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A true local monomial map sends the complete diagonal vector to its relabeled diagonal. -/
theorem generatedEighth_local_diagonal_action (f : localFiberSubgroup) (c : golayCode)
    (p : golayAutomorphismSubgroup) (hs : f.val.2 = golayMonomialPair (c, p))
    (d : Fin 24 → ℝ) :
    rhoLocal (localFiberIntoH f) (trialityDiagonalVector d) =
      trialityDiagonalVector (fun i => d (p.val.symm i)) := by
  suffices he : griessConwayEncode
      (rhoLocal (localFiberIntoH f) (trialityDiagonalVector d)) =
      griessConwayEncode (trialityDiagonalVector (fun i => d (p.val.symm i))) by
    have hh := congrArg griessConwayDecode he
    simpa only [griessConwayDecode_encode] using hh
  change griessConwayEncode (localGriessRepresentation f (trialityDiagonalVector d)) = _
  rw [localGriessRepresentation_encode, griessConwayEncode_diagonal,
    localConwayRawRepresentation_apply, griessConwayEncode_diagonal, hs,
    generatedEighth_monomial_diagonal, map_zero, map_zero]

/-- Inverse actual triality fixes every full diagonal vector. -/
theorem generatedEighth_inverse_triality_diagonal (d : Fin 24 → ℝ) :
    sExtra⁻¹ (trialityDiagonalVector d) = trialityDiagonalVector d := by
  have h := congrArg sExtra.symm (sExtra_diagonal d)
  have he : trialityDiagonalVector d = sExtra.symm (trialityDiagonalVector d) := by
    simpa only [LinearEquiv.symm_apply_apply] using h
  exact he.symm

/-- Forward actual triality conjugation leaves the original monomial diagonal action unchanged. -/
theorem generatedEighth_forward_diagonal_action (f k : localFiberSubgroup) (c : golayCode)
    (p : golayAutomorphismSubgroup) (hs : f.val.2 = golayMonomialPair (c, p))
    (ha : rhoLocal (localFiberIntoH k) =
      sExtra * rhoLocal (localFiberIntoH f) * sExtra⁻¹) (d : Fin 24 → ℝ) :
    conwayMatrixAction k.val.2 (Matrix.diagonal d) =
      Matrix.diagonal (fun i => d (p.val.symm i)) := by
  have hf : rhoLocal (localFiberIntoH k) (trialityDiagonalVector d) =
      trialityDiagonalVector (fun i => d (p.val.symm i)) := by
    rw [ha]
    simp only [LinearEquiv.mul_apply, generatedEighth_inverse_triality_diagonal,
      generatedEighth_local_diagonal_action f c p hs, sExtra_diagonal]
  have hm := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  rw [generatedFourth_local_matrix, griessConwayEncode_diagonal,
    griessConwayEncode_diagonal] at hm
  exact hm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

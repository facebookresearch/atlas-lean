/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinPlanData

/-! Exact finite inverse matrices and complete inverse signs of the original source profiles. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine inverse signed spin model, with the central quadratic sign retained. -/
def generatedSixthPermutationProfileInverseModel (k : Fin 3) : RepresentativeSpinModel :=
  representativeSpinRowsModel (generatedSixthPermutationProfileInverseCoordinateRows k)
    (generatedSixthPermutationProfileInversePhaseRows k)

set_option maxHeartbeats 2000000 in
-- Check actual inverse twelve-dimensional matrices for all three word profiles.
/-- Every recorded inverse coordinate matrix is a true inverse of the original spin pullback. -/
theorem generatedSixth_permutation_profile_inverse_matrix : ∀ k : Fin 3,
    (generatedSixthPermutationProfileModel k).coordinate *
      (generatedSixthPermutationProfileInverseModel k).coordinate = 1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check diagonal and polarized coefficients of the full actual inverse quadratic phase.
/-- Every inverse model retains exactly the original inverse spin phase polynomial. -/
theorem generatedSixth_permutation_profile_inverse_phase : ∀ k : Fin 3,
    (∀ i : Fin 12,
      ((generatedSixthPermutationProfileInverseModel k).coordinateᵀ *
        (generatedSixthPermutationProfileModel k).phase *
          (generatedSixthPermutationProfileInverseModel k).coordinate) i i =
        (generatedSixthPermutationProfileInverseModel k).phase i i) ∧
    (∀ i j : Fin 12,
      ((generatedSixthPermutationProfileInverseModel k).coordinateᵀ *
        (generatedSixthPermutationProfileModel k).phase *
          (generatedSixthPermutationProfileInverseModel k).coordinate) i j +
      ((generatedSixthPermutationProfileInverseModel k).coordinateᵀ *
        (generatedSixthPermutationProfileModel k).phase *
          (generatedSixthPermutationProfileInverseModel k).coordinate) j i =
        (generatedSixthPermutationProfileInverseModel k).phase i j +
          (generatedSixthPermutationProfileInverseModel k).phase j i) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

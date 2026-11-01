/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPlaneGeometry

/-! Integer certificates for the actual two-root span in the sixth watermark. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- The second actual shortest root is supported on coordinates sixteen and nineteen. -/
def generatedSixthPlaneSecondRoot (i : Fin 24) : ℤ :=
  4 * (if i = 16 then 1 else 0) - 4 * (if i = 19 then 1 else 0)

/-- The first linear-coordinate row in the rank-two numerator factorization. -/
def generatedSixthPlaneFirstRow (i : Fin 24) : ℤ :=
  (if i = 16 then 1 else 0) - 2 * (if i = 17 then 1 else 0) + (if i = 19 then 1 else 0)

/-- The second linear-coordinate row in the rank-two numerator factorization. -/
def generatedSixthPlaneSecondRow (i : Fin 24) : ℤ :=
  (if i = 16 then 1 else 0) + (if i = 17 then 1 else 0) - 2 * (if i = 19 then 1 else 0)

/-- Both genuine integer roots factor the ordinary rank-two projection numerator. -/
theorem generatedSixth_plane_numerator_factor :
    (4 : ℤ) • generatedSixthPlaneNumerator =
      Matrix.vecMulVec generatedSixthPlaneRoot generatedSixthPlaneFirstRow +
        Matrix.vecMulVec generatedSixthPlaneSecondRoot generatedSixthPlaneSecondRow := by
  decide +kernel

/-- The second root is also fixed with the exact original integer scaling. -/
theorem generatedSixth_plane_numerator_second_root :
    generatedSixthPlaneNumerator *ᵥ generatedSixthPlaneSecondRoot =
      (3 : ℤ) • generatedSixthPlaneSecondRoot := by
  decide +kernel

/-- The two actual short roots have integer norms32 and mutual pairing16. -/
theorem generatedSixth_plane_roots_norm_pairing :
    (∑ i, generatedSixthPlaneRoot i ^ 2) = 32 ∧
      (∑ i, generatedSixthPlaneSecondRoot i ^ 2) = 32 ∧
      (∑ i, generatedSixthPlaneRoot i * generatedSixthPlaneSecondRoot i) = 16 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves

/-! Original integer certificates for all seven spatial transitions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The original coordinate-frame image at every prefix. -/
def generatedEighthNormEightVectorData : Fin 8 → Fin 24 → ℤ :=
  ![![8, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![-4, -4, -4, -4, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -4, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -4,
      -4, 0, 0, 0, -4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -4, 0, 0, -4,
      -4, 0, 0, 0, -4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 4, 4, 0,
      2, 2, 2, 2, 2, 2, 2, 2],
    ![4, 2, 2, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, 2, 0,
      0, 2, 0, 2, 0, 4, 2, 2],
    ![4, 0, 0, 0, 2, 0, 0, 2,
      2, 0, 0, 2, 0, 0, 0, 0,
      0, 2, 0, 2, 0, 4, 2, 2],
    ![-2, -2, -2, -2, 0, -2, -2, 0,
      0, -2, -2, 0, 0, 0, 0, 0,
      2, 0, -2, 0, 4, 0, -2, -2]]

/-- Every prefix follows the actual Xi numerator or source permutation. -/
theorem generatedEighth_normEight_vector_certificate :
    (2 : ℕ) • generatedEighthNormEightVectorData 1 =
      co1XiNumerator *ᵥ generatedEighthNormEightVectorData 0 ∧
    generatedEighthNormEightVectorData 2 =
      golayIntegerPermute (omegaOrbitPermutation 0) (generatedEighthNormEightVectorData 1) ∧
    generatedEighthNormEightVectorData 3 =
      golayIntegerPermute (omegaOrbitPermutation 1) (generatedEighthNormEightVectorData 2) ∧
    (2 : ℕ) • generatedEighthNormEightVectorData 4 =
      co1XiNumerator *ᵥ generatedEighthNormEightVectorData 3 ∧
    generatedEighthNormEightVectorData 5 =
      golayIntegerPermute (omegaOrbitPermutation 0) (generatedEighthNormEightVectorData 4) ∧
    generatedEighthNormEightVectorData 6 =
      golayIntegerPermute (omegaOrbitPermutation 1) (generatedEighthNormEightVectorData 5) ∧
    (2 : ℕ) • generatedEighthNormEightVectorData 7 =
      co1XiNumerator *ᵥ generatedEighthNormEightVectorData 6 := by
  decide +kernel

/-- The checked actual final square sum is sixty-four. -/
theorem generatedEighth_normEight_data_square :
    leechSquareSum (generatedEighthNormEightVectorData 7) = 64 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

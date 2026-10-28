/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves

/-! Exact integer vector certificates for the literal eight-factor spatial word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The initial vector and each successive actual integer spatial image. -/
def generatedSixthNormEightVectorData : Fin 9 → Fin 24 → ℤ :=
  ![![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -4, -4, 4, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, -4, 0, 0],
    ![-4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, -4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 4, -4, 0, 4, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, -2, -2, -6, -2, 2, 0, 0, 0, 0],
    ![0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -2, 0, -6, -2, 2, -2, 0, 0, 0],
    ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -3, -3, 1, 5, 1, 1, 1, 1]]

/-- Every step uses the original Xi numerator or the genuine source permutation. -/
theorem generatedSixth_normEight_vector_certificate :
    generatedSixthNormEightVectorData 1 =
      golayIntegerPermute (omegaOrbitPermutation 0) (generatedSixthNormEightVectorData 0) ∧
    (2 : ℕ) • generatedSixthNormEightVectorData 2 =
      co1XiNumerator *ᵥ generatedSixthNormEightVectorData 1 ∧
    generatedSixthNormEightVectorData 3 =
      golayIntegerPermute (omegaOrbitPermutation 0) (generatedSixthNormEightVectorData 2) ∧
    generatedSixthNormEightVectorData 4 =
      golayIntegerPermute (omegaOrbitPermutation 1) (generatedSixthNormEightVectorData 3) ∧
    generatedSixthNormEightVectorData 5 =
      golayIntegerPermute (omegaOrbitPermutation 0) (generatedSixthNormEightVectorData 4) ∧
    (2 : ℕ) • generatedSixthNormEightVectorData 6 =
      co1XiNumerator *ᵥ generatedSixthNormEightVectorData 5 ∧
    generatedSixthNormEightVectorData 7 =
      golayIntegerPermute (omegaOrbitPermutation 1) (generatedSixthNormEightVectorData 6) ∧
    (2 : ℕ) • generatedSixthNormEightVectorData 8 =
      co1XiNumerator *ᵥ generatedSixthNormEightVectorData 7 := by
  decide +kernel

/-- The literal final vector has the genuine norm-eight integer square sum. -/
theorem generatedSixth_normEight_data_square :
    leechSquareSum (generatedSixthNormEightVectorData 8) = 64 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

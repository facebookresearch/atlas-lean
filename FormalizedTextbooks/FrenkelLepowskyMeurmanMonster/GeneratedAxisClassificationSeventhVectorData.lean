/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves

/-! Ordinary kernel certificates for the original seven-factor spatial action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The initial positive frame vector and each actual successive integer image. -/
def generatedSeventhNormEightVectorData : Fin 8 → Fin 24 → ℤ :=
  ![
    ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-4, -4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, -4, 0, 0, 0, -4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, -4, -4, 0, 0, 0, -4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, -4, -4, 0, 0, 0, -4, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 6, -2, 2, -2, 2, 0, 0, 0, 0],
    ![0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 6, 0, 2, -2, 2, -2, 0, 0, 0],
    ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, 3, -3, -3, 3, 1, 1, -3, 1, 1, 1, 1, 1]]

/-- Every successor is the actual Xi numerator or original source coordinate permutation. -/
theorem generatedSeventh_normEight_vector_certificate :
    (2 : ℕ) • generatedSeventhNormEightVectorData 1 =
      co1XiNumerator *ᵥ generatedSeventhNormEightVectorData 0 ∧
    generatedSeventhNormEightVectorData 2 =
      golayIntegerPermute (omegaOrbitPermutation 0) (generatedSeventhNormEightVectorData 1) ∧
    generatedSeventhNormEightVectorData 3 =
      golayIntegerPermute (omegaOrbitPermutation 1) (generatedSeventhNormEightVectorData 2) ∧
    generatedSeventhNormEightVectorData 4 =
      golayIntegerPermute (omegaOrbitPermutation 0) (generatedSeventhNormEightVectorData 3) ∧
    (2 : ℕ) • generatedSeventhNormEightVectorData 5 =
      co1XiNumerator *ᵥ generatedSeventhNormEightVectorData 4 ∧
    generatedSeventhNormEightVectorData 6 =
      golayIntegerPermute (omegaOrbitPermutation 1) (generatedSeventhNormEightVectorData 5) ∧
    (2 : ℕ) • generatedSeventhNormEightVectorData 7 =
      co1XiNumerator *ᵥ generatedSeventhNormEightVectorData 6 := by
  decide +kernel

/-- The final actual integer vector has square sum sixty-four. -/
theorem generatedSeventh_normEight_data_square :
    leechSquareSum (generatedSeventhNormEightVectorData 7) = 64 := by
  decide +kernel

/-- The five distinguished original coordinates have magnitude three; the other nineteen have
    one. -/
theorem generatedSeventh_normEight_data_magnitudes (i : Fin 24) :
    (generatedSeventhNormEightVectorData 7 i) ^ 2 =
      if i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 18 then 9 else 1 := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

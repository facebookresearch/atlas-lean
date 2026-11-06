/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthRepresentative

/-! A literal word in the two original Golay permutations transports the lower pairs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 20000

/-- The genuine Golay automorphism is a word in the two already checked permutations. -/
def generatedNinthSectionPermutation : golayAutomorphismSubgroup :=
  (omegaOrbitGolayPermutation 0)⁻¹ * omegaOrbitGolayPermutation 1 *
    omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 0 *
    omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 1 *
    (omegaOrbitGolayPermutation 0)⁻¹ * omegaOrbitGolayPermutation 1 *
    (omegaOrbitGolayPermutation 0)⁻¹ * omegaOrbitGolayPermutation 1 *
    omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 0 *
    omegaOrbitGolayPermutation 1 * omegaOrbitGolayPermutation 0 *
    omegaOrbitGolayPermutation 0

/-- Exact forward physical coordinates of the original permutation word. -/
def generatedNinthSectionPermutationForward : Fin 24 → Fin 24 :=
  ![7, 13, 2, 20, 3, 19, 1, 10, 22, 16, 8, 23, 17, 9, 15, 14, 12, 0, 21, 4, 18, 5, 11, 6]

/-- Exact inverse physical coordinates of the same original word. -/
def generatedNinthSectionPermutationInverse : Fin 24 → Fin 24 :=
  ![17, 6, 2, 4, 19, 21, 23, 0, 10, 13, 7, 22, 16, 1, 15, 14, 9, 12, 20, 5, 3, 18, 8, 11]

/-- Both finite coordinate tables are the actual forward and inverse source word. -/
theorem generatedNinth_section_permutation_coordinates : ∀ i : Fin 24,
    generatedNinthSectionPermutation.val i = generatedNinthSectionPermutationForward i ∧
      generatedNinthSectionPermutation.val.symm i =
        generatedNinthSectionPermutationInverse i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

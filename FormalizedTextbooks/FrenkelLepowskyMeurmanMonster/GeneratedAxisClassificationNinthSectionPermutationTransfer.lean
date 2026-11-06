/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionTransportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionCoordinates

/-! An explicit word in the original Golay permutations carries the two selected octads. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 20000

/-- Twelve original inverse Golay letters retain the physical forward discovery orientation. -/
def generatedNinthSpreadSectionPermutation : golayAutomorphismSubgroup :=
  (omegaOrbitGolayPermutation 1)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 1)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 1)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 1)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹

/-- Exact physical forward positions of the original twelve-letter permutation. -/
def generatedNinthSpreadSectionPermutationForward : Fin 24 → Fin 24 :=
  ![17, 18, 9, 11, 0, 2, 21, 20, 19, 16, 8, 10, 1, 3, 22, 23, 15, 6, 14, 5, 12, 7, 4, 13]

/-- The finite positions are exactly the actual original word. -/
theorem generatedNinth_spread_section_permutation_coordinates : ∀ i : Fin 24,
    generatedNinthSpreadSectionPermutation.val i =
      generatedNinthSpreadSectionPermutationForward i := by
  decide +kernel

/-- The actual permutation carries the recovered octad support to the original Fifth section. -/
theorem generatedNinth_spread_section_permutation_support : ∀ i : Fin 24,
    golayOctadWord generatedFifthFlagOctad (generatedNinthSpreadSectionPermutation.val i) =
      golayEncoder (golayLabelCoefficients generatedNinthSectionCode) i := by
  simp only [golayOctadWord, generatedFifthFlagOctad_label]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

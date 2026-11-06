/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootCatalogueActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Rooted

/-! The transported complete catalogue is the actual standard coordinate E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire original codeword is carried to the standard codeword by the genuine source word. -/
theorem generatedTenth_e7_root_catalogue_word :
    golayPermute generatedTenthE7RootCataloguePermutation.val⁻¹
      (golayOctadWord generatedFifthFlagOctad) = golayStandardOctad := by
  ext i
  change golayOctadWord generatedFifthFlagOctad
    (generatedTenthE7RootCataloguePermutation.val i) = golayStandardOctad i
  rw [generatedTenth_e7_root_catalogue_forward]
  have h : ∀ i : Fin 24, golayEncoder (golayLabelCoefficients 2052)
      (generatedTenthE7RootCatalogueForward i) = golayStandardOctad i := by
    decide +kernel
  simpa only [golayOctadWord, generatedFifthFlagOctad_label] using h i

/-- The full actual image section equals the full standard coordinate section. -/
theorem generatedTenth_e7_standard_e8_section_actual :
    generatedTenthE7StandardE8Section = generatedAxisE8CoordinateSection golayStandardOctad := by
  change generatedAxisE8ImageSection
    (golayPermutationIsometry generatedTenthE7RootCataloguePermutation⁻¹)
      (golayOctadWord generatedFifthFlagOctad) = _
  rw [generatedAxisE8_permutation_image]
  change generatedAxisE8CoordinateSection
    (golayPermute generatedTenthE7RootCataloguePermutation.val⁻¹
      (golayOctadWord generatedFifthFlagOctad)) = _
  rw [generatedTenth_e7_root_catalogue_word]

/-- Every actual integral vector in the complete section has exactly the first-eight support. -/
theorem generatedTenth_e7_standard_e8_section_mem (u : leechIntegral) :
    u ∈ generatedTenthE7StandardE8Section ↔ ∀ i : Fin 24, 8 ≤ i.val → u.val i = 0 := by
  rw [generatedTenth_e7_standard_e8_section_actual]
  change (∀ i, golayStandardOctad i = 0 → u.val i = 0) ↔ _
  constructor
  · intro h i hi
    apply h i
    simp [golayStandardOctad, show ¬ i.val < 8 by omega]
  · intro h i hi
    apply h i
    by_contra hn
    have hl : i.val < 8 := by omega
    simp [golayStandardOctad, hl] at hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

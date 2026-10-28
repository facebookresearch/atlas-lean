/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7CompanionCoverage

/-! Original source2343 is transported to the actual standard companion110 by the genuine pair word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- The actual standard companion source has the complete original eight-coordinate support. -/
theorem generatedTenth_e7_standard_companion_coordinate : ∀ i : Fin 24,
    golayEncoder (golayLabelCoefficients 110) i =
      if i = 4 ∨ i = 5 ∨ i = 8 ∨ i = 10 ∨ i = 13 ∨ i = 14 ∨ i = 22 ∨ i = 23
      then 1 else 0 := by
  decide +kernel

/-- The original inverse source is an actual member of the complete incident sector. -/
theorem generatedTenth_e7_companion_transport_source :
    (2343 : Fin 4096) ∈ generatedFeasibleContainingSelectedIncidentCodes 0 := by
  simp only [generatedFeasibleContainingSelectedIncidentCodes, golayOctads,
    Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

/-- Every coordinate of the original pair word binds its actual companion-code transport. -/
theorem generatedTenth_e7_companion_pair_word_coordinate :
    golayPermute (generatedTenthE7OctadPairWord 22).val
      (golayEncoder (golayLabelCoefficients 2343)) =
        golayEncoder (golayLabelCoefficients 110) := by
  decide +kernel

/-- The actual original label action transports source2343 to standard companion110 exactly. -/
theorem generatedTenth_e7_companion_pair_word_label :
    golayLabelPermutation (generatedTenthE7OctadPairWord 22) 2343 = 110 := by
  apply golayLabelCoefficients_injective
  apply golayEncoder_injective
  rw [golayLabelPermutation_word, generatedTenth_e7_companion_pair_word_coordinate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

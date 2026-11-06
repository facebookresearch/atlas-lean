/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSignSpace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionTransportData

/-! Exact actual Golay sign counts for the standard and transported octads. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Count all original Golay labels with zero bits on the eight standard coordinates.
/-- Exactly thirty-two original Golay labels vanish on the standard octad. -/
theorem generatedNinth_standard_octad_sign_labels_card :
    (generatedNinthOctadSignLabels 2063).card = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Count all original Golay labels on the actual destination support of the source transport.
/-- Exactly thirty-two original Golay labels vanish on the transported octad. -/
theorem generatedNinth_section_octad_sign_labels_card :
    (generatedNinthOctadSignLabels generatedNinthSectionCode).card = 32 := by
  decide +kernel

/-- The entire actual standard-octad sign subspace has order thirty-two. -/
theorem generatedNinth_standard_octad_sign_space_card :
    Nat.card (generatedNinthOctadSignSpace 2063) = 32 := by
  rw [generatedNinth_octad_sign_space_card, generatedNinth_standard_octad_sign_labels_card]

/-- The entire actual transported-octad sign subspace has order thirty-two. -/
theorem generatedNinth_section_octad_sign_space_card :
    Nat.card (generatedNinthOctadSignSpace generatedNinthSectionCode) = 32 := by
  rw [generatedNinth_octad_sign_space_card, generatedNinth_section_octad_sign_labels_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

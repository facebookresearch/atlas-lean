/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCoordinates

/-! The eight distinct candidate exceptional octad signs, in the original short dictionary.
Their actual coefficients are proved separately. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The eight candidate signs with large Fourier numerator in original octad459. -/
def generatedNinthOctadMarkedSigns : Finset (Fin 64) := {2, 13, 23, 24, 36, 43, 49, 62}

/-- The listed original exceptional octad signs are eight distinct addresses. -/
theorem generatedNinth_octad_marked_signs_card : generatedNinthOctadMarkedSigns.card = 8 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

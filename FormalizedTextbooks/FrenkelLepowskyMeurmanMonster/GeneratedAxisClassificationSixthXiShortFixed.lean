/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortCertificates

/-! Complete true signed source transport fixes the entire original preferred-short constituent. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual corrected Xi fixes all original short coordinates, including every zero row. -/
theorem generatedSixth_xi_short_fixed :
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1 =
      (griessConwayEncode generatedSixthAxis).2.1 := by
  apply generatedSixth_xi_short_fixed_of_nonzero_sources
  intro r hr
  obtain ⟨x, rfl⟩ := generatedSixth_xi_short_support_covered r hr
  obtain ⟨n, rfl⟩ := generatedSixth_xi_short_number_surjective x
  exact generatedSixth_xi_short_number_certificate n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

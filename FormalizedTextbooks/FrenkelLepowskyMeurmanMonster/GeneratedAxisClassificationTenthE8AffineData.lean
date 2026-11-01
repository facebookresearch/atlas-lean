/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8PointwiseCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadPointwiseCount

/-! Original Golay source words for the sixteen outside affine permutations
on the actual Tenth octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Five actual certified Golay stabilizer words carry the standard octad
to Tenth's octad. -/
def generatedTenthE8StandardPermutation : golayAutomorphismSubgroup :=
  golayStabilizerAutomorphism 5 * golayStabilizerAutomorphism 0 *
    golayStabilizerAutomorphism 57 * golayStabilizerAutomorphism 89 *
      golayStabilizerAutomorphism 98

/-- The full twenty-four-coordinate word action identifies the actual octad supports. -/
theorem generatedTenth_e8_standard_permutation_support : ∀ i : Fin 24,
    generatedTenthE8StandardPermutation.val i ∈ generatedTenthE7OctadSupport ↔ i.val < 8 := by
  decide +kernel

/-- The original sixteen corrected representatives transported by that genuine word. -/
def generatedTenthE8AffineRepresentative (j : Fin 16) : golayAutomorphismSubgroup :=
  generatedTenthE8StandardPermutation * generatedNinthStandardOctadRepresentative j *
    generatedTenthE8StandardPermutation⁻¹

set_option maxHeartbeats 4000000 in
-- Bind all twenty-four source coordinates of the complete transported identity word.
/-- The first complete actual transported representative is the identity. -/
theorem generatedTenth_e8_affine_zero : generatedTenthE8AffineRepresentative 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  change ∀ i : Fin 24, (generatedTenthE8AffineRepresentative 0).val i = i
  decide +kernel

/-- All sixteen actual source words are tested on the entire six-coordinate norm-twelve support. -/
theorem generatedTenth_e8_affine_line_support : ∀ j : Fin 16,
    (∀ i ∈ generatedTenthE7LineSupport,
      (generatedTenthE8AffineRepresentative j).val i ∈ generatedTenthE7LineSupport) ↔ j = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

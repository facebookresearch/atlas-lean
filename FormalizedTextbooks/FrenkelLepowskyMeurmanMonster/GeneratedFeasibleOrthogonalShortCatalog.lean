/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOrthogonalShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOrthogonalOctadCoordinates

/-! The complete original short-coordinate catalogue perpendicular to 4(e₀-e₁).
This finite catalogue counts 46,575 unsigned lines and 93,150 signed axis addresses.
Identification with the actual transition orbit is a separate geometric step. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All original pair, octad, and odd shortest-vector labels perpendicular to the root. -/
def generatedFeasibleOrthogonalShortLabels : Finset GriessShortIndex :=
  generatedFeasibleOrthogonalPairLabels.disjSum
    (generatedFeasibleOrthogonalOctadLabels.disjSum generatedFeasibleOrthogonalOddLabels)

/-- Catalogue membership is exactly equality of the actual two root coordinates. -/
theorem generatedFeasibleOrthogonalShortLabels_mem (r : GriessShortIndex) :
    r ∈ generatedFeasibleOrthogonalShortLabels ↔
      griessShortIntegral r 0 = griessShortIntegral r 1 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · simp only [generatedFeasibleOrthogonalShortLabels, Finset.inl_mem_disjSum,
      generatedFeasibleOrthogonalPairLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [generatedFeasibleOrthogonalShortLabels, Finset.inr_mem_disjSum,
      Finset.inl_mem_disjSum, generatedFeasibleOrthogonalOctadLabels,
      Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [generatedFeasibleOrthogonalShortLabels, Finset.inr_mem_disjSum]
    exact generatedFeasibleOrthogonalOddLabels_mem d j

/-- The full actual root-perpendicular shortest-vector catalogue has 46,575 lines. -/
theorem generatedFeasibleOrthogonalShortLabels_card :
    generatedFeasibleOrthogonalShortLabels.card = 46575 := by
  rw [generatedFeasibleOrthogonalShortLabels, Finset.card_disjSum, Finset.card_disjSum,
    generatedFeasibleOrthogonalPairLabels_card, generatedFeasibleOrthogonalOctadLabels_card,
    generatedFeasibleOrthogonalOddLabels_card]

/-- Both actual signed-short axis addresses over every root-perpendicular physical line. -/
def generatedFeasibleOrthogonalSignedShortLabels : Finset (GriessShortIndex × ZMod 2) :=
  generatedFeasibleOrthogonalShortLabels ×ˢ Finset.univ

/-- The complete physical signed-short catalogue has exactly 93,150 addresses. -/
theorem generatedFeasibleOrthogonalSignedShortLabels_card :
    generatedFeasibleOrthogonalSignedShortLabels.card = 93150 := by
  rw [generatedFeasibleOrthogonalSignedShortLabels, Finset.card_product,
    generatedFeasibleOrthogonalShortLabels_card, Finset.card_univ]
  norm_num [ZMod.card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

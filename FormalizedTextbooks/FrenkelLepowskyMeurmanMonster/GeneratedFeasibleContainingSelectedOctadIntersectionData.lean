/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSelectedOctadCodesData

/-! Complete original octad intersection counts relative to source label 2063. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The genuine increasing octad address, bound to its original twelve-bit code. -/
def generatedFeasibleContainingOctadSelectedWeight (o : Fin 759) : ℕ :=
  generatedFeasibleContainingCodeSelectedWeight (golayOctadLabel o)

/-- Original containing-pair octads grouped by their actual intersection with the source octad.
-/
def generatedFeasibleContainingSelectedIncidentOctads (k : Fin 3) : Finset (Fin 759) :=
  generatedFeasibleOctadContainingLabels.filter fun o =>
    generatedFeasibleContainingOctadSelectedWeight o = (![2, 4, 8] : Fin 3 → ℕ) k

/-- Original outside-pair octads grouped by their actual intersection with the source octad. -/
def generatedFeasibleContainingSelectedOutsideOctads (k : Fin 3) : Finset (Fin 759) :=
  generatedFeasibleOctadOutsideLabels.filter fun o =>
    generatedFeasibleContainingOctadSelectedWeight o = (![0, 2, 4] : Fin 3 → ℕ) k

/-- Exactly sixteen, sixty and one original incident octads have source intersection 2, 4 and 8.
-/
theorem generatedFeasibleContainingSelectedIncidentOctads_card (k : Fin 3) :
    (generatedFeasibleContainingSelectedIncidentOctads k).card =
      (![16, 60, 1] : Fin 3 → ℕ) k := by
  rw [generatedFeasibleContainingSelectedIncidentOctads,
    generatedFeasibleOctadContainingLabels, Finset.filter_filter]
  unfold generatedFeasibleContainingOctadSelectedWeight
  rw [generatedFeasibleOctadLabel_filter_card (fun d : Fin 4096 =>
    ((golayEncodedMask d.val).testBit 0 = true ∧
      (golayEncodedMask d.val).testBit 1 = true) ∧
        generatedFeasibleContainingCodeSelectedWeight d = (![2, 4, 8] : Fin 3 → ℕ) k)]
  exact generatedFeasibleContainingSelectedIncidentCodes_card k

/-- Exactly thirty, 240 and sixty original outside octads have source intersection 0, 2 and 4.
-/
theorem generatedFeasibleContainingSelectedOutsideOctads_card (k : Fin 3) :
    (generatedFeasibleContainingSelectedOutsideOctads k).card =
      (![30, 240, 60] : Fin 3 → ℕ) k := by
  rw [generatedFeasibleContainingSelectedOutsideOctads,
    generatedFeasibleOctadOutsideLabels, Finset.filter_filter]
  unfold generatedFeasibleContainingOctadSelectedWeight
  rw [generatedFeasibleOctadLabel_filter_card (fun d : Fin 4096 =>
    ((golayEncodedMask d.val).testBit 0 = false ∧
      (golayEncodedMask d.val).testBit 1 = false) ∧
        generatedFeasibleContainingCodeSelectedWeight d = (![0, 2, 4] : Fin 3 → ℕ) k)]
  exact generatedFeasibleContainingSelectedOutsideCodes_card k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

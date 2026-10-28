/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7CompanionWeight

/-! The actual sixteen-companion pointwise orbit covers the entire original incident sector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete original sixteen-code sector has actual set cardinality16. -/
theorem generatedTenth_e7_companion_sector_card :
    Nat.card (generatedFeasibleContainingSelectedIncidentCodes 0 : Set (Fin 4096)) = 16 := by
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact generatedFeasibleContainingSelectedIncidentCodes_card 0

/-- The genuine pointwise permutation orbit covers the entire original sixteen-code sector. -/
theorem generatedTenth_e7_companion_pointwise_orbit_actual :
    MulAction.orbit generatedNinthStandardOctadPointwise (2306 : Fin 4096) =
      (generatedFeasibleContainingSelectedIncidentCodes 0 : Set (Fin 4096)) := by
  apply Set.eq_of_subset_of_ncard_le generatedTenth_e7_companion_pointwise_orbit_subset
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    generatedTenth_e7_companion_sector_card, generatedTenth_e7_companion_pointwise_orbit_card]

/-- Every original incident companion is attained by the entire actual pointwise group. -/
theorem generatedTenth_e7_companion_pointwise_reaches (d : Fin 4096)
    (hd : d ∈ generatedFeasibleContainingSelectedIncidentCodes 0) :
    ∃ p : generatedNinthStandardOctadPointwise, golayLabelPermutation p.val 2306 = d := by
  have h : d ∈ MulAction.orbit generatedNinthStandardOctadPointwise (2306 : Fin 4096) := by
    rw [generatedTenth_e7_companion_pointwise_orbit_actual]
    exact hd
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

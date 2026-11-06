/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightGeneratorCriterion

/-! Genuine order attainment from whole-axis fixers with an explicitly allowed central Q phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- An actual original local candidate with a genuine central extraspecial sign correction. -/
def generatedRootEightGeneratorCentralCandidate (j : Fin 12) (c : ZMod 2) : H :=
  inclQ (qCentral c) * generatedRootEightGeneratorCandidate j

/-- Each genuine central correction leaves the entire original Conway projection unchanged. -/
theorem generatedRootEight_generator_central_candidate_projection (j : Fin 12) (c : ZMod 2) :
    projH (generatedRootEightGeneratorCentralCandidate j c) =
      generatedRootEightCanonicalQuotientConjugation (generatedRootEightGeneratorSpatial j) := by
  rw [generatedRootEightGeneratorCentralCandidate, map_mul, projH_inclQ, one_mul,
    generatedRootEight_generator_candidate_projection]

/-- A complete-axis fixer for each original generator, allowing an actual central Q sign,
attains the entire required original Conway image. -/
theorem generatedRootEight_generator_central_fixation_projected_order
    (hfix : ∀ j : Fin 12, ∃ c : ZMod 2,
      rhoLocal (inclQ (qCentral c) * generatedRootEightGeneratorCandidate j)
        generatedFifthRootEightAxis = generatedFifthRootEightAxis) :
    Nat.card generatedFifthRootEightProjectedAxisStabilizer = 88704000 := by
  let S := generatedFifthRootEightProjectedAxisStabilizer.comap
    generatedRootEightCanonicalQuotientConjugation
  have hS : ∀ j : Fin 12, generatedRootEightGeneratorSpatial j ∈ S := by
    intro j
    obtain ⟨c, hc⟩ := hfix j
    change generatedRootEightCanonicalQuotientConjugation (generatedRootEightGeneratorSpatial j) ∈
      generatedFifthRootEightProjectedAxisStabilizer
    rw [← generatedRootEight_generator_central_candidate_projection j c]
    exact ⟨⟨generatedRootEightGeneratorCentralCandidate j c, hc⟩, rfl⟩
  have hM := generatedRootEight_generators_contain_mate_group S hS
  have hr : generatedRootEightMateQuotient.range ≤ generatedFifthRootEightProjectedAxisStabilizer := by
    rintro _ ⟨g, rfl⟩
    exact hM g.property
  let : Finite Co1 := co1_finite
  apply Nat.le_antisymm
  · exact generatedFifthRootEight_projected_card_le_spatial.trans_eq
      generatedFifthRootEight_Co1_spatial_stabilizer_card
  · rw [← generatedRootEight_mate_quotient_range_card]
    exact Subgroup.card_le_of_le hr

/-- The twelve genuine central-phase-flexible full-axis fixers give the exact original local order. -/
theorem generatedRootEight_generator_central_fixation_local_order
    (hfix : ∀ j : Fin 12, ∃ c : ZMod 2,
      rhoLocal (inclQ (qCentral c) * generatedRootEightGeneratorCandidate j)
        generatedFifthRootEightAxis = generatedFifthRootEightAxis) :
    Nat.card generatedFifthRootEightLocalAxisStabilizer = 177408000 := by
  exact generatedFifthRootEight_local_order_iff_projected_order.mpr
    (generatedRootEight_generator_central_fixation_projected_order hfix)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

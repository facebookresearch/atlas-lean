/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverMateActualFixers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightGeneratorCriterion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReductionActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightLocalOrbitLower

/-! Exact original root-eight local cardinalities from genuine whole-axis fixer attainment. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Every genuine canonical whole-axis fixer attains its actual transported original Conway value. -/
theorem generatedRootEight_original_projection_of_canonical_fixer (g : leechIsomSubgroup)
    (hfix : ∃ h : H, projH h = QuotientGroup.mk' signsSubgroup g ∧
      rhoLocal h generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis) :
    generatedRootEightCanonicalQuotientConjugation g ∈ generatedFifthRootEightProjectedAxisStabilizer := by
  obtain ⟨h, hp, hf⟩ := hfix
  obtain ⟨k, hk, hfixk⟩ := generatedRootEight_canonical_positive_fixer_transfer h hf
  refine ⟨⟨k, hfixk⟩, ?_⟩
  change projH k = generatedRootEightCanonicalQuotientConjugation g
  rw [hk, generatedRootEight_canonical_positive_projection, hp]
  rfl

/-- All actual positive-root two-companion quotient values are attained by original whole-axis fixers. -/
theorem generatedRootEight_actual_mate_quotient_range_le :
    generatedRootEightMateQuotient.range ≤ generatedFifthRootEightProjectedAxisStabilizer := by
  let F := leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion
  let S := generatedFifthRootEightProjectedAxisStabilizer.comap
    generatedRootEightCanonicalQuotientConjugation
  have hK : leechNormSixHS100PairPointStabilizer.map F.subtype ≤ S := by
    rw [← generatedRootEight_mathieu_reduced_in_conway, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact generatedRootEight_original_projection_of_canonical_fixer _
      (generatedRootEight_mathieu_actual_fixer_projection j)
  have hS : ∀ j : Fin 12, generatedRootEightGeneratorSpatial j ∈ S := by
    intro j
    unfold generatedRootEightGeneratorSpatial
    split_ifs with hj hj10
    · apply hK
      rw [← leechNormSixHS100Mathieu_generated_in_conway]
      exact Subgroup.subset_closure ⟨⟨j.val, hj⟩, rfl⟩
    · exact generatedRootEight_original_projection_of_canonical_fixer _
        generatedRootEight_mover_actual_fixer_projection
    · exact generatedRootEight_original_projection_of_canonical_fixer _
        generatedRootEight_mate_actual_fixer_projection
  have hM := generatedRootEight_generators_contain_mate_group S hS
  rintro _ ⟨g, rfl⟩
  exact hM g.property

/-- The actual original whole-axis Conway projection has exactly88704000 attained values. -/
theorem generatedRootEight_actual_projected_stabilizer_card :
    Nat.card generatedFifthRootEightProjectedAxisStabilizer = 88704000 := by
  let : Finite Co1 := co1_finite
  apply Nat.le_antisymm
  · exact generatedFifthRootEight_projected_card_le_spatial.trans_eq
      generatedFifthRootEight_Co1_spatial_stabilizer_card
  · rw [← generatedRootEight_mate_quotient_range_card]
    exact Subgroup.card_le_of_le generatedRootEight_actual_mate_quotient_range_le

/-- The complete original root-eight local stabilizer has exactly177408000 genuine elements. -/
theorem generatedRootEight_actual_local_stabilizer_card :
    Nat.card generatedFifthRootEightLocalAxisStabilizer = 177408000 :=
  generatedFifthRootEight_local_order_iff_projected_order.mpr
    generatedRootEight_actual_projected_stabilizer_card

/-- The actual original root-eight local axis orbit has its exact size from the proved stabilizer order. -/
theorem generatedRootEight_actual_local_axis_orbit_card :
    Nat.card (MulAction.orbit H generatedFifthRootEightAxis) = 786389785840189440 := by
  have h := generatedFifthRootEightLocalAxisStabilizer.card_mul_index
  rw [generatedRootEight_actual_local_stabilizer_card, local_h_card_exact] at h
  have hi : generatedFifthRootEightLocalAxisStabilizer.index = 786389785840189440 := by omega
  rw [generatedFifthRootEightLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSignLifts

/-! The exact physical fourth-flag closure contains every required monomial sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each actual four-word permutation is in the exact physical flag-generator closure. -/
theorem generatedFourthFlagGenerator_monomial_mem (k : Fin 4) :
    (generatedFourthMonomialFiber k).val.2 ∈ generatedFourthPhysicalFlagGeneratorSubgroup :=
  Subgroup.subset_closure (Or.inl ⟨k, rfl⟩)

/-- The normalized spatial generator is in its actual generated subgroup. -/
theorem generatedFourthFlagGenerator_normalized_mem :
    generatedFourthFlagNormalizedLift.val.2 ∈ generatedFourthPhysicalFlagGeneratorSubgroup :=
  Subgroup.subset_closure (Or.inr rfl)

/-- The actual cube sign belongs to this same closure by the verified spatial cube. -/
theorem generatedFourthFlagGenerator_cube_mem :
    golaySignIsometry generatedFourthFlagCubeSignCode ∈
      generatedFourthPhysicalFlagGeneratorSubgroup := by
  rw [← generatedFourth_flag_cube_isometry]
  exact generatedFourthPhysicalFlagGeneratorSubgroup.pow_mem
    generatedFourthFlagGenerator_normalized_mem 3

/-- The previously counted sign-generating monomial subgroup is in the exact flag closure. -/
theorem generatedFourthFlagGenerator_monomial_le :
    generatedFourthMonomialPhysicalSubgroup ≤ generatedFourthPhysicalFlagGeneratorSubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro e (⟨k, rfl⟩ | rfl)
  · exact generatedFourthFlagGenerator_monomial_mem k
  · exact generatedFourthFlagGenerator_cube_mem

/-- All actual equal-pair Golay signs lie in the exact flag-generator subgroup. -/
theorem generatedFourthFlagGenerator_equal_sign_le :
    generatedFourthFlagEqualSignSubgroup ≤ generatedFourthPhysicalFlagGeneratorSubgroup :=
  generatedFourth_monomial_equal_sign_subgroup_le.trans
    generatedFourthFlagGenerator_monomial_le

/-- Every generated physical element fixes the genuine E8-section and short-line flag. -/
theorem generatedFourthFlagGenerator_le_flag :
    generatedFourthPhysicalFlagGeneratorSubgroup ≤ generatedAxisE8ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort := by
  apply (Subgroup.closure_le _).mpr
  rintro e (⟨k, rfl⟩ | rfl)
  · exact generatedFourth_monomial_flag_mem k
  · exact generatedFourth_flag_lift_mem

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

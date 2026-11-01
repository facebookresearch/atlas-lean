/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLocalSpatialProjection

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeProjectionGeneration

/-! Three complete actual source projection values suffice for the original entire subgroup
and its genuine projected stabilizer cardinality lower bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Any subgroup containing the three genuine original source values contains the whole group. -/
theorem generatedNinth_lower_spin_three_group_le (P : Subgroup Co1)
    (h : ∀ g : Fin 3, generatedNinthLowerSpinActualGenerator
      (generatedNinthLowerSpinThreeCandidateIndex g) ∈ P) :
    generatedNinthLowerSpinActualGroup ≤ P := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, rfl⟩
  exact generatedNinth_lower_spin_three_projection_candidates_mem P h i

/-- Fixing the whole actual axis with three genuine lifts attains all original source values. -/
theorem generatedNinth_lower_spin_three_axis_group_le
    (h : ∀ g : Fin 3, generatedNinthLowerSpinDirectLocal
      (generatedNinthLowerSpinThreeCandidateIndex g) ∈ generatedNinthLocalAxisStabilizer) :
    generatedNinthLowerSpinActualGroup ≤ generatedNinthProjectedAxisStabilizer := by
  apply generatedNinth_lower_spin_three_group_le
  intro g
  refine ⟨⟨generatedNinthLowerSpinDirectLocal (generatedNinthLowerSpinThreeCandidateIndex g),
    h g⟩, ?_⟩
  exact generatedNinth_lower_spin_direct_projection_eq_original _

/-- Three complete genuine actual-axis fixers imply the entire original order lower bound. -/
theorem generatedNinth_lower_spin_three_actual_projected_card_lower
    (h : ∀ g : Fin 3, generatedNinthLowerSpinDirectLocal
      (generatedNinthLowerSpinThreeCandidateIndex g) ∈ generatedNinthLocalAxisStabilizer) :
    92897280 ≤ Nat.card generatedNinthProjectedAxisStabilizer := by
  let : Finite Co1 := co1_finite
  have hi := generatedNinth_lower_spin_three_axis_group_le h
  exact generatedNinth_lower_spin_actual_group_card_lower.trans
    (Nat.card_le_card_of_injective (Subgroup.inclusion hi) (Subgroup.inclusion_injective hi))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

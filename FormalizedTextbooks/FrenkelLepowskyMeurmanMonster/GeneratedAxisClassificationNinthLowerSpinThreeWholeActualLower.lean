/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeAxisFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeFixerClosure
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerActualInput

/-! Complete actual original source bindings and three full-axis lifts yield the entire
genuine projected stabilizer lower bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem spatial_coordinate (i : Fin 11) (j k : Fin 24) :
    (generatedNinthLowerSpinTensorSpatialDenominator i : ℝ) *
      (generatedNinthLowerSpinDirectIsometry i).val (Pi.single k 1) j =
        (generatedNinthLowerSpinTensorSpatialNumerator i j k : ℝ) := by
  exact congrArg (fun a : Matrix (Fin 24) (Fin 24) ℝ => a j k)
    (generatedNinth_lower_spin_direct_isometry_numerator i)

/-- Every selected genuine oriented lift fixes the whole original actual Ninth axis. -/
theorem generatedNinth_lower_spin_three_whole_actual_axis_fix (g : Fin 3) :
    localGriessRepresentation (generatedNinthLowerSpinDirectFiber
      (generatedNinthLowerSpinThreeCandidateIndex g)) generatedNinthAxis = generatedNinthAxis :=
  generatedNinth_lower_spin_three_axis_fix_of_source_caches g (spatial_coordinate _)
    generatedNinth_actual_tensor_input generatedNinth_actual_short_input

/-- The three actual whole-axis fixers attain all eleven genuine original source projections. -/
theorem generatedNinth_lower_spin_three_whole_actual_membership (g : Fin 3) :
    generatedNinthLowerSpinDirectLocal (generatedNinthLowerSpinThreeCandidateIndex g) ∈
      generatedNinthLocalAxisStabilizer :=
  generatedNinth_lower_spin_three_axis_local_membership g (spatial_coordinate _)
    generatedNinth_actual_tensor_input generatedNinth_actual_short_input

/-- The entire genuine original source subgroup lies in the actual projected stabilizer. -/
theorem generatedNinth_lower_spin_three_whole_actual_group_le_axis :
    generatedNinthLowerSpinActualGroup ≤ generatedNinthProjectedAxisStabilizer :=
  generatedNinth_lower_spin_three_axis_group_le
    generatedNinth_lower_spin_three_whole_actual_membership

/-- Three complete actual-axis lifts suffice for the original 512×181440 order lower bound. -/
theorem generatedNinth_lower_spin_three_whole_actual_projected_card_lower :
    92897280 ≤ Nat.card generatedNinthProjectedAxisStabilizer :=
  generatedNinth_lower_spin_three_actual_projected_card_lower
    generatedNinth_lower_spin_three_whole_actual_membership

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

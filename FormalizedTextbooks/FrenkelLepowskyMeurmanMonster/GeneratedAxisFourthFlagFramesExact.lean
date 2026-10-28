/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesConsequences
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGeneration

/-! Unconditional full fourth-axis flag generation and actual local orbit counts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual five physical generators generate the entire genuine fourth flag stabilizer. -/
theorem generatedFourthFlagFrames_generator_eq_flag :
    generatedFourthPhysicalFlagGeneratorSubgroup = generatedAxisE8ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort :=
  generatedFourthFlagGenerator_eq_flag_of_card_inputs generatedFourthPermutationFourSubgroup
    generatedFourth_permutation_four_card generatedFourthFlagFrames_permutation_mem
    generatedFourthFlagFramesCount_orbit_lower

/-- Every physical fourth flag stabilizer has a genuine full-axis fixing local lift. -/
theorem generatedFourthFlagFrames_projection_surjective :
    Function.Surjective generatedFourthLocalAxisProjection :=
  generatedFourthFlagGenerator_projection_surjective generatedFourthFlagFrames_generator_eq_flag

/-- The full actual fourth H stabilizer has order 95126814720. -/
theorem generatedFourthFlagFrames_stabilizer_card :
    Nat.card generatedFourthLocalAxisStabilizer = 95126814720 :=
  generatedFourthFlagFrames_local_stabilizer_card generatedFourthFlagFrames_generator_eq_flag

/-- Exactly 1466587938816000 actual axes occur in the fourth local H orbit. -/
theorem generatedFourthFlagFrames_axis_orbit_card :
    Nat.card (MulAction.orbit H generatedFourthAxis) = 1466587938816000 :=
  generatedFourthFlagGenerator_axis_orbit_card generatedFourthFlagFrames_generator_eq_flag

/-- The entire fourth physical matrix fiber consists of the genuine Q orbit. -/
theorem generatedFourthFlagFrames_matrix_fiber_eq_q_orbit :
    generatedFourthMatrixFiber = generatedFourthQAxisOrbit :=
  generatedFourthFlagFrames_matrix_fiber_eq generatedFourthFlagFrames_generator_eq_flag

/-- Exactly 262144 actual full axes occur in the fourth physical matrix fiber. -/
theorem generatedFourthFlagFrames_actual_matrix_fiber_card :
    Nat.card generatedFourthMatrixFiber = 262144 :=
  generatedFourthFlagFrames_matrix_fiber_card generatedFourthFlagFrames_generator_eq_flag

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthProjectedSystem
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthProjectedSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationFull

/-! The complete actual fifth-axis stabilizer and local orbit from genuine whole-axis lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All six original spatial generators have genuine whole-axis lifts in the actual projection. -/
theorem generatedFifthProjectedAxisStabilizer_permutation_mem (k : Fin 6) :
    QuotientGroup.mk' signsSubgroup
      (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k)) ∈
        generatedFifthProjectedAxisStabilizer := by
  have h := generatedFifthProjectedAxisStabilizer_mem_of_lift
    (generatedFifthMonomialPermutationCorrectedFiber k)
    (generatedFifth_monomial_permutation_full_fixed k)
  change projH (localFiberIntoH (generatedFifthMonomialPermutationCorrectedFiber k)) ∈
    generatedFifthProjectedAxisStabilizer at h
  rwa [generatedFifth_monomial_permutation_corrected_projection] at h

/-- The actual full fifth-axis projection equals the independently identified system stabilizer. -/
theorem generatedFifthProjectedAxisStabilizer_eq_system :
    generatedFifthProjectedAxisStabilizer = generatedFifthFrameSystemCo1Stabilizer :=
  generatedFifthProjectedAxisStabilizer_eq_system_of_generators
    generatedFifthProjectedAxisStabilizer_sign_mem
    generatedFifthProjectedAxisStabilizer_permutation_mem

/-- The entire actual fifth-axis stabilizer in H has its exact order. -/
theorem generatedFifth_local_stabilizer_card :
    Nat.card generatedFifthLocalAxisStabilizer = 21139292160 :=
  generatedFifth_local_stabilizer_card_of_system generatedFifthProjectedAxisStabilizer_eq_system

/-- The whole fifth-axis orbit under the actual local group H has its exact cardinality. -/
theorem generatedFifth_local_axis_orbit_card :
    Nat.card (MulAction.orbit H generatedFifthAxis) = 6599645724672000 :=
  generatedFifth_local_axis_orbit_card_of_system generatedFifthProjectedAxisStabilizer_eq_system

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

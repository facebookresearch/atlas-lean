/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeTensorAddressCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeTensorReplayCertificates

/-! Whole compact tensor action from actual source boundaries
and complete coordinate replay packets. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Every compact genuine spin factor preserves the entire candidate tensor under its exact
rational spatial action. Separate source bindings identify the actual Ninth tensor. -/
theorem generatedNinth_lower_spin_three_tensor_circuit (g : Fin 3) (j : Fin 24) :
    (generatedNinthLowerSpinCompact (generatedNinthLowerSpinThreeCandidateIndex g)).val
      (nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorSpatialInteger
        (generatedNinthLowerSpinThreeCandidateIndex g) n j)) =
        (generatedNinthLowerSpinTensorSpatialDenominator
          (generatedNinthLowerSpinThreeCandidateIndex g) : ℝ) •
          nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorInputInteger n j) := by
  exact generatedNinth_lower_spin_tensor_column_replay
    (generatedNinthLowerSpinThreeCandidateIndex g) j
    (generatedNinth_lower_spin_three_tensor_addresses g)
    generatedNinth_lower_spin_tensor_fourier_addresses
    (generatedNinth_lower_spin_three_tensor_replay_start g j)
    (generatedNinth_lower_spin_three_tensor_replay_step g j)
    (generatedNinth_lower_spin_three_tensor_replay_finish g j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

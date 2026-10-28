/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeTensorAddressCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeTensorReplayCertificates

/-! Whole compact tensor action from all actual source boundary and full-coordinate replay packets. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Every compact genuine spin factor preserves the entire candidate tensor under its exact
rational spatial action. Separate source bindings identify this tensor with the actual Twelfth axis. -/
theorem generatedTwelfth_three_spin_tensor_circuit (i : Fin 3) (j : Fin 24) :
    (generatedTwelfthSpinCompact (generatedTwelfthThreeCandidateIndex i)).val
      (nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorSpatialInteger (generatedTwelfthThreeCandidateIndex i) n j)) =
        (generatedTwelfthSpinTensorSpatialDenominator (generatedTwelfthThreeCandidateIndex i) : ℝ) •
          nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorInputInteger n j) := by
  exact generatedTwelfth_spin_tensor_column_replay (generatedTwelfthThreeCandidateIndex i) j
    (generatedTwelfth_three_spin_tensor_addresses i)
    generatedTwelfth_spin_tensor_fourier_addresses
    (generatedTwelfth_three_spin_tensor_replay_start i j)
    (generatedTwelfth_three_spin_tensor_replay_step i j)
    (generatedTwelfth_three_spin_tensor_replay_finish i j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

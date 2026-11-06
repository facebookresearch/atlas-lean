/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorFourierAddresses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorAddressPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket00Start
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket00Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket00Finish

/-! Every complete original tensor replay equation for genuine candidate 0. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem complete_step (j : Fin 24) (s : ℕ) (p : Fin 12 × Fin 12)
    (hp : (generatedTwelfthSpinTensorPairWord 0)[s]? = some p) (n : Fin 4096) :
    generatedTwelfthSpinTensorFourierInteger p.1
      (generatedTwelfthSpinTensorFourierInteger p.2
        (fun m => generatedTwelfthSpinTensorStageInteger 0 s m j)) n =
          2 * generatedTwelfthSpinTensorStageInteger 0 (s + 1) n j := by
  cases s with
    | zero =>
      have he : p = (0, 1) := by
        simpa [generatedTwelfthSpinTensorPairWord] using hp.symm
      subst p
      exact generatedTwelfth_spin_tensor_replay_packet_00_pair00 j n
    | succ s =>
      simp [generatedTwelfthSpinTensorPairWord] at hp

/-- This actual candidate's whole integer tensor has its complete genuine compact action. -/
theorem generatedTwelfth_candidate_tensor_circuit_00 (j : Fin 24) :
    (generatedTwelfthSpinCompact 0).val
      (nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorSpatialInteger 0 n j)) =
        (generatedTwelfthSpinTensorSpatialDenominator 0 : ℝ) •
          nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorInputInteger n j) := by
  exact generatedTwelfth_spin_tensor_column_replay 0 j
    generatedTwelfth_spin_tensor_address_packet_00
    generatedTwelfth_spin_tensor_fourier_addresses
    (generatedTwelfth_spin_tensor_replay_packet_00_start j)
    (fun s p hp n => complete_step j s p hp n)
    (generatedTwelfth_spin_tensor_replay_packet_00_finish j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

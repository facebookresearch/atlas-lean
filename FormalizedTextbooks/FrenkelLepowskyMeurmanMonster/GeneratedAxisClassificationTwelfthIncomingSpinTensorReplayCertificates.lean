/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorReplayPacket00Start
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorReplayPacket00Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorReplayPacket00Pair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorReplayPacket00Pair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorReplayPacket00Pair03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorReplayPacket00Finish

/-! Every full tensor cache start, paired Fourier transition and final boundary equation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All full-column starting packets retain the spatial numerator and actual pre-boundary. -/
theorem generatedTwelfth_incoming_spin_tensor_replay_start : ∀ i j n,
    generatedTwelfthIncomingSpinTensorStageInteger i 0 n j =
      generatedTwelfthIncomingSpinTensorPreInteger i
        (fun m => generatedTwelfthIncomingSpinTensorSpatialInteger i m j) n := by
  intro i j n
  fin_cases i
  · exact generatedTwelfth_incoming_spin_tensor_replay_packet_00_start j n

/-- All paired stages cover every genuine Fourier factor in its exact application order. -/
theorem generatedTwelfth_incoming_spin_tensor_replay_step : ∀ i j s p,
    (generatedTwelfthIncomingSpinTensorPairWord i)[s]? = some p → ∀ n,
      generatedTwelfthIncomingSpinTensorFourierInteger p.1
        (generatedTwelfthIncomingSpinTensorFourierInteger p.2
          (fun m => generatedTwelfthIncomingSpinTensorStageInteger i s m j)) n =
            2 * generatedTwelfthIncomingSpinTensorStageInteger i (s + 1) n j := by
  intro i j s p hp n
  fin_cases i
  · cases s with
    | zero =>
      have he : p = (6, 7) := by
        simpa [generatedTwelfthIncomingSpinTensorPairWord] using hp.symm
      subst p
      exact generatedTwelfth_incoming_spin_tensor_replay_packet_00_pair00 j n
    | succ s =>
      cases s with
      | zero =>
        have he : p = (4, 5) := by
          simpa [generatedTwelfthIncomingSpinTensorPairWord] using hp.symm
        subst p
        exact generatedTwelfth_incoming_spin_tensor_replay_packet_00_pair01 j n
      | succ s =>
        cases s with
        | zero =>
          have he : p = (2, 3) := by
            simpa [generatedTwelfthIncomingSpinTensorPairWord] using hp.symm
          subst p
          exact generatedTwelfth_incoming_spin_tensor_replay_packet_00_pair02 j n
        | succ s =>
          cases s with
          | zero =>
            have he : p = (0, 1) := by
              simpa [generatedTwelfthIncomingSpinTensorPairWord] using hp.symm
            subst p
            exact generatedTwelfth_incoming_spin_tensor_replay_packet_00_pair03 j n
          | succ s =>
            simp [generatedTwelfthIncomingSpinTensorPairWord] at hp

/-- Every full final packet equals the spatial denominator times the complete input tensor. -/
theorem generatedTwelfth_incoming_spin_tensor_replay_finish : ∀ i j n,
    generatedTwelfthIncomingSpinTensorPostInteger i
      (fun m => generatedTwelfthIncomingSpinTensorStageInteger i
        (generatedTwelfthIncomingSpinTensorPairWord i).length m j) n =
          generatedTwelfthIncomingSpinTensorOutputInteger n j := by
  intro i j n
  fin_cases i
  · exact generatedTwelfth_incoming_spin_tensor_replay_packet_00_finish j n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

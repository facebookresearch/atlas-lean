/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeProjectionGeneration

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket00Start
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket00Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket00Finish
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket09Start
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket09Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket09Pair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket09Pair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket09Pair03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket09Pair04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket09Finish
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket10Start
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket10Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket10Pair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket10Pair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket10Pair03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket10Pair04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorReplayPacket10Finish

/-! Every full tensor cache start, paired Fourier transition and final boundary equation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All full-column starting packets retain the spatial numerator and actual pre-boundary. -/
theorem generatedNinth_lower_spin_three_tensor_replay_start : ∀ g : Fin 3, ∀ j n,
    generatedNinthLowerSpinTensorStageInteger (generatedNinthLowerSpinThreeCandidateIndex g) 0 n j =
      generatedNinthLowerSpinTensorPreInteger (generatedNinthLowerSpinThreeCandidateIndex g)
        (fun m => generatedNinthLowerSpinTensorSpatialInteger
          (generatedNinthLowerSpinThreeCandidateIndex g) m j) n := by
  intro g j n
  fin_cases g
  · exact generatedNinth_lower_spin_tensor_replay_packet_00_start j n
  · exact generatedNinth_lower_spin_tensor_replay_packet_09_start j n
  · exact generatedNinth_lower_spin_tensor_replay_packet_10_start j n

/-- All paired stages cover every genuine Fourier factor in its exact application order. -/
theorem generatedNinth_lower_spin_three_tensor_replay_step : ∀ g : Fin 3, ∀ j s p,
    (generatedNinthLowerSpinTensorPairWord (generatedNinthLowerSpinThreeCandidateIndex g))[s]?
      = some p → ∀ n,
      generatedNinthLowerSpinTensorFourierInteger p.1
        (generatedNinthLowerSpinTensorFourierInteger p.2
          (fun m => generatedNinthLowerSpinTensorStageInteger
            (generatedNinthLowerSpinThreeCandidateIndex g) s m j)) n =
            2 * generatedNinthLowerSpinTensorStageInteger
              (generatedNinthLowerSpinThreeCandidateIndex g) (s + 1) n j := by
  intro g j s p hp n
  fin_cases g
  · cases s with
    | zero =>
      have he : p = (0, 1) := by
        simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
      subst p
      exact generatedNinth_lower_spin_tensor_replay_packet_00_pair00 j n
    | succ s =>
      simp [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] at hp
  · cases s with
    | zero =>
      have he : p = (8, 9) := by
        simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
      subst p
      exact generatedNinth_lower_spin_tensor_replay_packet_09_pair00 j n
    | succ s =>
      cases s with
      | zero =>
        have he : p = (6, 7) := by
          simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
        subst p
        exact generatedNinth_lower_spin_tensor_replay_packet_09_pair01 j n
      | succ s =>
        cases s with
        | zero =>
          have he : p = (4, 5) := by
            simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
          subst p
          exact generatedNinth_lower_spin_tensor_replay_packet_09_pair02 j n
        | succ s =>
          cases s with
          | zero =>
            have he : p = (2, 3) := by
              simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
            subst p
            exact generatedNinth_lower_spin_tensor_replay_packet_09_pair03 j n
          | succ s =>
            cases s with
            | zero =>
              have he : p = (0, 1) := by
                simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
              subst p
              exact generatedNinth_lower_spin_tensor_replay_packet_09_pair04 j n
            | succ s =>
              simp [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] at hp
  · cases s with
    | zero =>
      have he : p = (8, 9) := by
        simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
      subst p
      exact generatedNinth_lower_spin_tensor_replay_packet_10_pair00 j n
    | succ s =>
      cases s with
      | zero =>
        have he : p = (6, 7) := by
          simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
        subst p
        exact generatedNinth_lower_spin_tensor_replay_packet_10_pair01 j n
      | succ s =>
        cases s with
        | zero =>
          have he : p = (4, 5) := by
            simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
          subst p
          exact generatedNinth_lower_spin_tensor_replay_packet_10_pair02 j n
        | succ s =>
          cases s with
          | zero =>
            have he : p = (2, 3) := by
              simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
            subst p
            exact generatedNinth_lower_spin_tensor_replay_packet_10_pair03 j n
          | succ s =>
            cases s with
            | zero =>
              have he : p = (0, 1) := by
                simpa [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] using hp.symm
              subst p
              exact generatedNinth_lower_spin_tensor_replay_packet_10_pair04 j n
            | succ s =>
              simp [generatedNinthLowerSpinTensorPairWord, generatedNinthLowerSpinThreeCandidateIndex] at hp

/-- Every full final packet equals the spatial denominator times the complete input tensor. -/
theorem generatedNinth_lower_spin_three_tensor_replay_finish : ∀ g : Fin 3, ∀ j n,
    generatedNinthLowerSpinTensorPostInteger (generatedNinthLowerSpinThreeCandidateIndex g)
      (fun m => generatedNinthLowerSpinTensorStageInteger
        (generatedNinthLowerSpinThreeCandidateIndex g)
        (generatedNinthLowerSpinTensorPairWord (generatedNinthLowerSpinThreeCandidateIndex
          g)).length m j) n =
          (generatedNinthLowerSpinTensorSpatialDenominator
            (generatedNinthLowerSpinThreeCandidateIndex g) : ℤ) *
            generatedNinthLowerSpinTensorInputInteger n j := by
  intro g j n
  fin_cases g
  · exact generatedNinth_lower_spin_tensor_replay_packet_00_finish j n
  · exact generatedNinth_lower_spin_tensor_replay_packet_09_finish j n
  · exact generatedNinth_lower_spin_tensor_replay_packet_10_finish j n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

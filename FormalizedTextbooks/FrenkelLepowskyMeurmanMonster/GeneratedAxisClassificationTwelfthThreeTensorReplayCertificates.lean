/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeCandidateIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket00Start
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket00Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket00Finish
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket01Start
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket01Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket01Pair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket01Pair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket01Finish
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket02Start
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket02Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket02Pair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket02Pair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorReplayPacket02Finish

/-! Whole original replay equations for the three required genuine compatible candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- All full-column starting packets retain the spatial numerator and actual pre-boundary. -/
theorem generatedTwelfth_three_spin_tensor_replay_start : ∀ (i : Fin 3) j n,
    generatedTwelfthSpinTensorStageInteger (generatedTwelfthThreeCandidateIndex i) 0 n j =
      generatedTwelfthSpinTensorPreInteger (generatedTwelfthThreeCandidateIndex i)
        (fun m => generatedTwelfthSpinTensorSpatialInteger (generatedTwelfthThreeCandidateIndex i) m j) n := by
  intro i j n
  fin_cases i
  · exact generatedTwelfth_spin_tensor_replay_packet_00_start j n
  · exact generatedTwelfth_spin_tensor_replay_packet_01_start j n
  · exact generatedTwelfth_spin_tensor_replay_packet_02_start j n


/-- All paired stages cover every genuine Fourier factor in its exact application order. -/
theorem generatedTwelfth_three_spin_tensor_replay_step : ∀ (i : Fin 3) j s p,
    (generatedTwelfthSpinTensorPairWord (generatedTwelfthThreeCandidateIndex i))[s]? = some p → ∀ n,
      generatedTwelfthSpinTensorFourierInteger p.1
        (generatedTwelfthSpinTensorFourierInteger p.2
          (fun m => generatedTwelfthSpinTensorStageInteger (generatedTwelfthThreeCandidateIndex i) s m j)) n =
            2 * generatedTwelfthSpinTensorStageInteger (generatedTwelfthThreeCandidateIndex i) (s + 1) n j := by
  intro i j s p hp n
  fin_cases i
  · cases s with
    | zero =>
      have he : p = (0, 1) := by
        simpa [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] using hp.symm
      subst p
      exact generatedTwelfth_spin_tensor_replay_packet_00_pair00 j n
    | succ s =>
      simp [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] at hp
  · cases s with
    | zero =>
      have he : p = (4, 5) := by
        simpa [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] using hp.symm
      subst p
      exact generatedTwelfth_spin_tensor_replay_packet_01_pair00 j n
    | succ s =>
      cases s with
      | zero =>
        have he : p = (2, 3) := by
          simpa [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] using hp.symm
        subst p
        exact generatedTwelfth_spin_tensor_replay_packet_01_pair01 j n
      | succ s =>
        cases s with
        | zero =>
          have he : p = (0, 1) := by
            simpa [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] using hp.symm
          subst p
          exact generatedTwelfth_spin_tensor_replay_packet_01_pair02 j n
        | succ s =>
          simp [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] at hp
  · cases s with
    | zero =>
      have he : p = (4, 5) := by
        simpa [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] using hp.symm
      subst p
      exact generatedTwelfth_spin_tensor_replay_packet_02_pair00 j n
    | succ s =>
      cases s with
      | zero =>
        have he : p = (2, 3) := by
          simpa [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] using hp.symm
        subst p
        exact generatedTwelfth_spin_tensor_replay_packet_02_pair01 j n
      | succ s =>
        cases s with
        | zero =>
          have he : p = (0, 1) := by
            simpa [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] using hp.symm
          subst p
          exact generatedTwelfth_spin_tensor_replay_packet_02_pair02 j n
        | succ s =>
          simp [generatedTwelfthSpinTensorPairWord, generatedTwelfthThreeCandidateIndex] at hp

/-- Every full final packet equals the spatial denominator times the complete input tensor. -/
theorem generatedTwelfth_three_spin_tensor_replay_finish : ∀ (i : Fin 3) j n,
    generatedTwelfthSpinTensorPostInteger (generatedTwelfthThreeCandidateIndex i)
      (fun m => generatedTwelfthSpinTensorStageInteger (generatedTwelfthThreeCandidateIndex i)
        (generatedTwelfthSpinTensorPairWord (generatedTwelfthThreeCandidateIndex i)).length m j) n =
          (generatedTwelfthSpinTensorSpatialDenominator (generatedTwelfthThreeCandidateIndex i) : ℤ) *
            generatedTwelfthSpinTensorInputInteger n j := by
  intro i j n
  fin_cases i
  · exact generatedTwelfth_spin_tensor_replay_packet_00_finish j n
  · exact generatedTwelfth_spin_tensor_replay_packet_01_finish j n
  · exact generatedTwelfth_spin_tensor_replay_packet_02_finish j n


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

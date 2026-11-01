/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket03Part10

/-! All original chronological stages and full central coordinates of source 3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check every actual initial, chronological-letter or final full-Q coordinate obligation.
private theorem base : ∀ j : Fin 24, generatedNinthLowerSpinSourceQReplayBaseCondition 3 j := by
  unfold generatedNinthLowerSpinSourceQReplayBaseCondition
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check every actual initial, chronological-letter or final full-Q coordinate obligation.
private theorem letters : ∀ n : Fin 378,
    generatedNinthLowerSpinSourceQReplayLetterCondition 3 n := by
  unfold generatedNinthLowerSpinSourceQReplayLetterCondition
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check every actual initial, chronological-letter or final full-Q coordinate obligation.
private theorem finish : ∀ j : Fin 24, generatedNinthLowerSpinSourceQReplayFinishCondition 3 j := by
  unfold generatedNinthLowerSpinSourceQReplayFinishCondition
  decide +kernel

/-- Every original source stage is one bounded primitive replay on its literal full-Q input. -/
private theorem steps (n : Fin 378) (j : Fin 24) :
    generatedNinthLowerSpinSourceQReplayStepCondition 3 n j := by
  intro hn
  have hlen : (generatedNinthLowerSpinSourceWord 3).length = 174 := by decide
  rw [hlen] at hn
  generalize hb : n.val / 16 = b
  have hbound : b < 11 := by omega
  interval_cases b
  · have hz : 0 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_00
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 16 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_01
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 32 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_02
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 48 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_03
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 64 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_04
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 80 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_05
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 96 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_06
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 112 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_07
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 128 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_08
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 144 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_09
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn
  · have hz : 160 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_03_part_10
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 3 n j from
      by simpa only [hz] using h) hn

/-- All twenty-four complete source-word images follow from bounded exact primitive stages. -/
theorem generatedNinth_lower_spin_source_q_replay_generator_03 (j : Fin 24) :
    generatedNinthLowerSpinSourceQEvaluation 3 (qCoordinateGenerator j) =
      generatedNinthLowerSpinQImage 3 j :=
  generatedNinth_lower_spin_source_q_replay_generic 3 j (base j) letters
    (fun n => steps n j) (finish j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

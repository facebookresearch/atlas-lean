/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacket05Part19

/-! All original chronological stages and full central coordinates of source 5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check every actual initial, chronological-letter or final full-Q coordinate obligation.
private theorem base : ∀ j : Fin 24, generatedNinthLowerSpinSourceQReplayBaseCondition 5 j := by
  unfold generatedNinthLowerSpinSourceQReplayBaseCondition
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check every actual initial, chronological-letter or final full-Q coordinate obligation.
private theorem letters : ∀ n : Fin 378,
    generatedNinthLowerSpinSourceQReplayLetterCondition 5 n := by
  unfold generatedNinthLowerSpinSourceQReplayLetterCondition
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check every actual initial, chronological-letter or final full-Q coordinate obligation.
private theorem finish : ∀ j : Fin 24, generatedNinthLowerSpinSourceQReplayFinishCondition 5 j := by
  unfold generatedNinthLowerSpinSourceQReplayFinishCondition
  decide +kernel

/-- Every original source stage is one bounded primitive replay on its literal full-Q input. -/
private theorem steps (n : Fin 378) (j : Fin 24) :
    generatedNinthLowerSpinSourceQReplayStepCondition 5 n j := by
  intro hn
  have hlen : (generatedNinthLowerSpinSourceWord 5).length = 314 := by decide
  rw [hlen] at hn
  generalize hb : n.val / 16 = b
  have hbound : b < 20 := by omega
  interval_cases b
  · have hz : 0 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_00
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 16 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_01
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 32 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_02
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 48 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_03
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 64 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_04
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 80 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_05
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 96 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_06
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 112 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_07
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 128 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_08
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 144 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_09
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 160 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_10
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 176 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_11
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 192 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_12
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 208 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_13
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 224 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_14
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 240 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_15
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 256 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_16
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 272 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_17
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 288 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_18
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn
  · have hz : 304 + n.val % 16 = n.val := by omega
    have h := generatedNinth_lower_spin_source_q_replay_packet_05_part_19
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ j (by simpa only [Fin.val_mk, hz] using hn)
    exact (show generatedNinthLowerSpinSourceQReplayStepCondition 5 n j from
      by simpa only [hz] using h) hn

/-- All twenty-four complete source-word images follow from bounded exact primitive stages. -/
theorem generatedNinth_lower_spin_source_q_replay_generator_05 (j : Fin 24) :
    generatedNinthLowerSpinSourceQEvaluation 5 (qCoordinateGenerator j) =
      generatedNinthLowerSpinQImage 5 j :=
  generatedNinth_lower_spin_source_q_replay_generic 5 j (base j) letters
    (fun n => steps n j) (finish j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

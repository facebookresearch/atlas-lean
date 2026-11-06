/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSourceWordComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQSourceWordFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQBasis00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQBasis01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQBasis04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayCertificate00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayCertificate01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayCertificate04

/-! The three original Mathieu words used in the reduced generator retain their entire Q actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Compare all original binary coordinates and their complete central phases.
/-- Every recorded compact coordinate agrees with the entire original source replay. -/
theorem generatedRootEight_m22_compact_basis_source_00 : ∀ j : Fin 24,
    generatedRootEightCompactBasisImage 0 j =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData00 ⟨7, by omega⟩ j) := by
  decide +kernel

/-- The original Mathieu source has the complete compact action on the genuine group Q. -/
theorem generatedRootEight_m22_compact_source_condition_00 :
    generatedRootEightCompactSourceCondition 0 := by
  apply generatedRootEight_compact_source_condition_of_word 0
    (generatedRootEightQSourceWords 0)
  · change generatedRootEightQSourceWordFiber (Fin.castAdd 1 (0 : Fin 12)) =
      generatedRootEightCompactSourceFiber (Fin.castAdd 2 (0 : Fin 12))
    rw [generatedRootEight_Q_source_generator_fiber,
      generatedRootEight_compact_source_generator]
  · intro j
    exact (generatedRootEight_compact_q_basis_00 j).trans
      ((generatedRootEight_m22_compact_basis_source_00 j).trans
        (generatedRootEight_Q_replay_00_actual j).symm)

set_option maxHeartbeats 4000000 in
-- Compare all original binary coordinates and their complete central phases.
/-- Every recorded compact coordinate agrees with the entire original source replay. -/
theorem generatedRootEight_m22_compact_basis_source_01 : ∀ j : Fin 24,
    generatedRootEightCompactBasisImage 1 j =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData01 ⟨11, by omega⟩ j) := by
  decide +kernel

/-- The original Mathieu source has the complete compact action on the genuine group Q. -/
theorem generatedRootEight_m22_compact_source_condition_01 :
    generatedRootEightCompactSourceCondition 1 := by
  apply generatedRootEight_compact_source_condition_of_word 1
    (generatedRootEightQSourceWords 1)
  · change generatedRootEightQSourceWordFiber (Fin.castAdd 1 (1 : Fin 12)) =
      generatedRootEightCompactSourceFiber (Fin.castAdd 2 (1 : Fin 12))
    rw [generatedRootEight_Q_source_generator_fiber,
      generatedRootEight_compact_source_generator]
  · intro j
    exact (generatedRootEight_compact_q_basis_01 j).trans
      ((generatedRootEight_m22_compact_basis_source_01 j).trans
        (generatedRootEight_Q_replay_01_actual j).symm)

set_option maxHeartbeats 4000000 in
-- Compare all original binary coordinates and their complete central phases.
/-- Every recorded compact coordinate agrees with the entire original source replay. -/
theorem generatedRootEight_m22_compact_basis_source_04 : ∀ j : Fin 24,
    generatedRootEightCompactBasisImage 4 j =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData04 ⟨20, by omega⟩ j) := by
  decide +kernel

/-- The original Mathieu source has the complete compact action on the genuine group Q. -/
theorem generatedRootEight_m22_compact_source_condition_04 :
    generatedRootEightCompactSourceCondition 4 := by
  apply generatedRootEight_compact_source_condition_of_word 4
    (generatedRootEightQSourceWords 4)
  · change generatedRootEightQSourceWordFiber (Fin.castAdd 1 (4 : Fin 12)) =
      generatedRootEightCompactSourceFiber (Fin.castAdd 2 (4 : Fin 12))
    rw [generatedRootEight_Q_source_generator_fiber,
      generatedRootEight_compact_source_generator]
  · intro j
    exact (generatedRootEight_compact_q_basis_04 j).trans
      ((generatedRootEight_m22_compact_basis_source_04 j).trans
        (generatedRootEight_Q_replay_04_actual j).symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

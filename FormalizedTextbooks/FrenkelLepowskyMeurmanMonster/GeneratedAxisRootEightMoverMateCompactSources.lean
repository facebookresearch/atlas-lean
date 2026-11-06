/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSourceWordComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQSourceWordFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQBasis10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQBasis11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayCertificate11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayCertificate10

/-! The mover and mate retain their complete original Q actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

set_option maxHeartbeats 4000000 in
-- Compare all full binary images and the original central phases.
/-- Every original mover basis value equals the complete original word replay. -/
theorem generatedRootEight_m22_compact_basis_source_10 : ∀ j : Fin 24,
    generatedRootEightCompactBasisImage 10 j =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData10 ⟨170, by omega⟩ j) := by
  decide +kernel

/-- The original mover generator has its complete genuine compact Q action. -/
theorem generatedRootEight_m22_compact_source_condition_10 :
    generatedRootEightCompactSourceCondition 10 := by
  apply generatedRootEight_compact_source_condition_of_word 10
    (generatedRootEightQSourceWords 10)
  · change generatedRootEightQSourceWordFiber (Fin.castAdd 1 (10 : Fin 12)) =
      generatedRootEightCompactSourceFiber (Fin.castAdd 2 (10 : Fin 12))
    rw [generatedRootEight_Q_source_generator_fiber,
      generatedRootEight_compact_source_generator]
  · intro j
    exact (generatedRootEight_compact_q_basis_10 j).trans
      ((generatedRootEight_m22_compact_basis_source_10 j).trans
        (generatedRootEight_Q_replay_10_actual j).symm)


set_option maxHeartbeats 4000000 in
-- Compare all full binary images and the original central phases.
/-- Every original mate basis value equals the complete original word replay. -/
theorem generatedRootEight_m22_compact_basis_source_11 : ∀ j : Fin 24,
    generatedRootEightCompactBasisImage 11 j =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData11 ⟨10, by omega⟩ j) := by
  decide +kernel

/-- The original mate generator has its complete genuine compact Q action. -/
theorem generatedRootEight_m22_compact_source_condition_11 :
    generatedRootEightCompactSourceCondition 11 := by
  apply generatedRootEight_compact_source_condition_of_word 11
    (generatedRootEightQSourceWords 11)
  · change generatedRootEightQSourceWordFiber (Fin.castAdd 1 (11 : Fin 12)) =
      generatedRootEightCompactSourceFiber (Fin.castAdd 2 (11 : Fin 12))
    rw [generatedRootEight_Q_source_generator_fiber,
      generatedRootEight_compact_source_generator]
  · intro j
    exact (generatedRootEight_compact_q_basis_11 j).trans
      ((generatedRootEight_m22_compact_basis_source_11 j).trans
        (generatedRootEight_Q_replay_11_actual j).symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

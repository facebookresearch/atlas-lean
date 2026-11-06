/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSourceWordComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQSourceWordFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQBasis08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayCertificate08

/-! The second reduced Mathieu source retains the full original Q action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Compare all full binary images and the original central phases.
/-- Every second reduced Mathieu basis value equals the complete original word replay. -/
theorem generatedRootEight_m22_compact_basis_source_08 : ∀ j : Fin 24,
    generatedRootEightCompactBasisImage 8 j =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData08 ⟨231, by omega⟩ j) := by
  decide +kernel

/-- The second reduced Mathieu generator has its complete genuine compact Q action. -/
theorem generatedRootEight_m22_compact_source_condition_08 :
    generatedRootEightCompactSourceCondition 8 := by
  apply generatedRootEight_compact_source_condition_of_word 8
    (generatedRootEightQSourceWords 8)
  · change generatedRootEightQSourceWordFiber (Fin.castAdd 1 (8 : Fin 12)) =
      generatedRootEightCompactSourceFiber (Fin.castAdd 2 (8 : Fin 12))
    rw [generatedRootEight_Q_source_generator_fiber,
      generatedRootEight_compact_source_generator]
  · intro j
    exact (generatedRootEight_compact_q_basis_08 j).trans
      ((generatedRootEight_m22_compact_basis_source_08 j).trans
        (generatedRootEight_Q_replay_08_actual j).symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

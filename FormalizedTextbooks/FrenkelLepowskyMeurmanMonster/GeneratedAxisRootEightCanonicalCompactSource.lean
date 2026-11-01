/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQBasis12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayCertificate12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQSourceWordFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSourceFibers

/-! The canonical compact normalizer retains the complete original word's Q action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Compare every full Q coordinate, including its actual central coefficient.
/-- The final original canonical replay agrees with every recorded compact basis image. -/
theorem generatedRootEight_canonical_compact_basis_source : ∀ j : Fin 24,
    generatedRootEightCompactBasisImage 12 j =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData12 ⟨135, by omega⟩ j) := by
  decide +kernel

/-- The compact canonical spin has exactly the entire original canonical Q action. -/
theorem generatedRootEight_canonical_compact_source_condition :
    generatedRootEightCompactSourceCondition 12 := by
  apply generatedRootEight_compact_source_condition_of_basis
  intro j
  rw [generatedRootEight_compact_source_canonical]
  have hw := generatedRootEight_Q_word_actual (generatedRootEightQSourceWords 12)
    (qCoordinateGenerator j)
  change spinConjugation (generatedRootEightQSourceWordFiber 12).val.1
    (qCoordinateGenerator j) = _ at hw
  rw [generatedRootEight_Q_source_canonical_fiber] at hw
  exact (generatedRootEight_compact_conjugation 12 _).trans
    ((generatedRootEight_compact_q_basis_12 j).trans
      ((generatedRootEight_canonical_compact_basis_source j).trans
        ((generatedRootEight_Q_replay_12_actual j).symm.trans hw.symm)))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

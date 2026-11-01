/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayFiniteCertificate12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQFiniteWordReplay

/-! Complete original word 12 is bound to its certified full-Q prefix replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source word has its complete recorded number of letters. -/
theorem generatedRootEight_Q_replay_12_length :
    (generatedRootEightQSourceWords 12).length = 135 := by
  decide +kernel

/-- The entire original word has its full-Q image at every basis generator. -/
theorem generatedRootEight_Q_replay_12_actual (j : Fin 24) :
    generatedRootEightQWordImage (generatedRootEightQSourceWords 12) (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData12 ⟨135, by omega⟩ j) := by
  exact generatedRootEight_Q_finite_word_replay _ 135
    generatedRootEight_Q_replay_12_length generatedRootEightQReplayLetterLookup12
    generatedRootEightQReplayData12 generatedRootEight_Q_replay_12_letters
    generatedRootEight_Q_replay_12_base generatedRootEight_Q_replay_12_steps j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

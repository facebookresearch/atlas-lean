/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayFiniteCertificate10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQFiniteWordReplay

/-! Complete original word 10 is bound to its certified full-Q prefix replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source word has its complete recorded number of letters. -/
theorem generatedRootEight_Q_replay_10_length :
    (generatedRootEightQSourceWords 10).length = 170 := by
  decide +kernel

/-- The entire original word has its full-Q image at every basis generator. -/
theorem generatedRootEight_Q_replay_10_actual (j : Fin 24) :
    generatedRootEightQWordImage (generatedRootEightQSourceWords 10) (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData10 ⟨170, by omega⟩ j) := by
  exact generatedRootEight_Q_finite_word_replay _ 170
    generatedRootEight_Q_replay_10_length generatedRootEightQReplayLetterLookup10
    generatedRootEightQReplayData10 generatedRootEight_Q_replay_10_letters
    generatedRootEight_Q_replay_10_base generatedRootEight_Q_replay_10_steps j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

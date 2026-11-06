/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayFiniteCertificate07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQFiniteWordReplay

/-! Complete original word 7 is bound to its certified full-Q prefix replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source word has its complete recorded number of letters. -/
theorem generatedRootEight_Q_replay_07_length :
    (generatedRootEightQSourceWords 7).length = 109 := by
  decide +kernel

/-- The entire original word has its full-Q image at every basis generator. -/
theorem generatedRootEight_Q_replay_07_actual (j : Fin 24) :
    generatedRootEightQWordImage (generatedRootEightQSourceWords 7) (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData07 ⟨109, by omega⟩ j) := by
  exact generatedRootEight_Q_finite_word_replay _ 109
    generatedRootEight_Q_replay_07_length generatedRootEightQReplayLetterLookup07
    generatedRootEightQReplayData07 generatedRootEight_Q_replay_07_letters
    generatedRootEight_Q_replay_07_base generatedRootEight_Q_replay_07_steps j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

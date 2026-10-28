/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayFiniteCertificate11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQFiniteWordReplay

/-! Complete original word 11 is bound to its certified full-Q prefix replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source word has its complete recorded number of letters. -/
theorem generatedRootEight_Q_replay_11_length :
    (generatedRootEightQSourceWords 11).length = 10 := by
  decide +kernel

/-- The entire original word has its full-Q image at every basis generator. -/
theorem generatedRootEight_Q_replay_11_actual (j : Fin 24) :
    generatedRootEightQWordImage (generatedRootEightQSourceWords 11) (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData11 ⟨10, by omega⟩ j) := by
  exact generatedRootEight_Q_finite_word_replay _ 10
    generatedRootEight_Q_replay_11_length generatedRootEightQReplayLetterLookup11
    generatedRootEightQReplayData11 generatedRootEight_Q_replay_11_letters
    generatedRootEight_Q_replay_11_base generatedRootEight_Q_replay_11_steps j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQReplayFiniteCertificate08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQFiniteWordReplay

/-! Complete original word 8 is bound to its certified full-Q prefix replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source word has its complete recorded number of letters. -/
theorem generatedRootEight_Q_replay_08_length :
    (generatedRootEightQSourceWords 8).length = 231 := by
  decide +kernel

/-- The entire original word has its full-Q image at every basis generator. -/
theorem generatedRootEight_Q_replay_08_actual (j : Fin 24) :
    generatedRootEightQWordImage (generatedRootEightQSourceWords 8) (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitivePackedQ
        (generatedRootEightQReplayData08 ⟨231, by omega⟩ j) := by
  exact generatedRootEight_Q_finite_word_replay _ 231
    generatedRootEight_Q_replay_08_length generatedRootEightQReplayLetterLookup08
    generatedRootEightQReplayData08 generatedRootEight_Q_replay_08_letters
    generatedRootEight_Q_replay_08_base generatedRootEight_Q_replay_08_steps j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

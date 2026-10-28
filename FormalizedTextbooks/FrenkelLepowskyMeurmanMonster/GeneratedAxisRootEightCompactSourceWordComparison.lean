/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSourceFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPackedAction

/-! Full original word images identify compatible compact source actions without expansion. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full-Q word agreement at all original coordinates proves the complete compact condition. -/
theorem generatedRootEight_compact_source_condition_of_word (i : Fin 14)
    (w : List (Fin 11))
    (hw : ((w.map generatedRootEightQPrimitiveFiber).prod) =
      generatedRootEightCompactSourceFiber i)
    (hc : ∀ j : Fin 24, generatedRootEightCompactQImage i (qCoordinateGenerator j) =
      generatedRootEightQWordImage w (qCoordinateGenerator j)) :
    generatedRootEightCompactSourceCondition i := by
  apply generatedRootEight_compact_source_condition_of_basis
  intro j
  have ha := generatedRootEight_Q_word_actual w (qCoordinateGenerator j)
  rw [hw] at ha
  exact (generatedRootEight_compact_conjugation i _).trans ((hc j).trans ha.symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

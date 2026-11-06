/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStageCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStageCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStageChain
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQImage

/-! All complete original stage certificates close the genuine final source word image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original one-step coordinate image is checked with its full central phase. -/
theorem generatedAxisGlobalOddFifthQStageStep (k : Fin 2) (n : Fin 30) (i : Fin 24) :
    generatedAxisGlobalOddFifthQStageCoordinate k n i =
      generatedAxisGlobalOddFifthQStageCache k ⟨n.val + 1, by omega⟩ i := by
  fin_cases k
  · exact generatedAxisGlobalOddFifthQStageCheck00 n i
  · exact generatedAxisGlobalOddFifthQStageCheck01 n i

/-- Every final cached coordinate image is the complete actual original comparison image. -/
theorem generatedAxisGlobalOddFifthQStageFinal_actual (k : Fin 2) (i : Fin 24) :
    generatedAxisGlobalOddFifthQImage k (qCoordinateGenerator i) =
      generatedAxisGlobalOddFifthQCache k i := by
  rw [← generatedAxisGlobalOddFifthQImage_actual]
  exact generatedAxisGlobalOddFifthQStageCache_actual k i generatedAxisGlobalOddFifthQStageStep

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

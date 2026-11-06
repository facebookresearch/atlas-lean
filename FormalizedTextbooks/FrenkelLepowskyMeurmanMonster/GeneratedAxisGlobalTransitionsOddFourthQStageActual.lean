/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQStageCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQStageCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQStageCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQStageCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQStageChain

/-! All complete original stage certificates close the genuine final source word image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original one-step coordinate image is checked with its full central phase. -/
theorem generatedAxisGlobalOddFourthQStageStep (k : Fin 4) (n : Fin 20) (i : Fin 24) :
    generatedAxisGlobalOddFourthQStageCoordinate k n i =
      generatedAxisGlobalOddFourthQStageCache k ⟨n.val + 1, by omega⟩ i := by
  fin_cases k
  · exact generatedAxisGlobalOddFourthQStageCheck00 n i
  · exact generatedAxisGlobalOddFourthQStageCheck01 n i
  · exact generatedAxisGlobalOddFourthQStageCheck02 n i
  · exact generatedAxisGlobalOddFourthQStageCheck03 n i

/-- Every final cached coordinate image is the complete actual original comparison image. -/
theorem generatedAxisGlobalOddFourthQStageFinal_actual (k : Fin 4) (i : Fin 24) :
    generatedAxisGlobalOddFourthQImage k (qCoordinateGenerator i) =
      generatedAxisGlobalOddFourthQCache k i := by
  unfold generatedAxisGlobalOddFourthQImage
  rw [generatedAxisGlobalOddFourthQStageWord_generator k i generatedAxisGlobalOddFourthQStageStep]
  exact generatedAxisGlobalOddFourthQStageFinal k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

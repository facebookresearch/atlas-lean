/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQStageActual

/-! Complete actual coordinate and central-phase checks for one original comparison word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 10000

/-- All 24 source images, including their full original central phases. -/
theorem generatedAxisGlobalOddFourthQCache03_certificate (i : Fin 24) :
    generatedAxisGlobalOddFourthQImage 3 (qCoordinateGenerator i) =
      generatedAxisGlobalOddFourthQCache 3 i :=
  generatedAxisGlobalOddFourthQStageFinal_actual 3 i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

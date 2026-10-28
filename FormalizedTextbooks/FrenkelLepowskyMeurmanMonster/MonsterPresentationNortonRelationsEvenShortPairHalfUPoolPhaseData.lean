/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete forward-U central coefficients of the stored genuine preferred-Q pool masks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The full positive Q element encoded by the original stored pool mask. -/
def monsterNortonPairHalfUPoolEncodedQ (i : Fin 1552) : Q :=
  ⟨ofAdd (fun j : Fin 24 =>
    if (monsterNortonPairHalfUPoolInputMask i).testBit j.val then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 128000000 in
-- Check every full central coefficient through the genuine actual forward-U Q evaluator.
/-- Actual U gives positive central phase on each complete encoded pool Q element. -/
theorem monsterNortonPairHalfUPoolEncodedPhase_actual (i : Fin 1552) :
    toAdd (spinConjugation monsterNortonUFiber.val.1
      (monsterNortonPairHalfUPoolEncodedQ i)).coeff = 0 := by
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq,
    monsterNortonUQFastImage_selected_phase]
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

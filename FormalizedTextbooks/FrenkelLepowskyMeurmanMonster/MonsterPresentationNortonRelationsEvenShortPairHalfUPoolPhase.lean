/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual positive central phases of the 1552 preferred U transport images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolInputQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolPhaseData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every true pool image has its genuine positive preferred-Q phase. -/
theorem monsterNortonPairHalfUPoolPhase_actual (i : Fin 1552) :
    toAdd (spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonPairHalfUPoolInput i))).coeff = 0 := by
  rw [monsterNortonPairHalfUPoolInputQ_actual]
  exact monsterNortonPairHalfUPoolEncodedPhase_actual i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

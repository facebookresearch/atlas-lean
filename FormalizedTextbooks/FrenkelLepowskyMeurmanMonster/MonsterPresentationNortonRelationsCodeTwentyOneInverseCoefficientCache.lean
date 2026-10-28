/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual phase cache for the code-twentyone inverse-sixth packet coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneMixedCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual V polar phase evaluated directly on a complete original source Q lift. -/
def monsterNortonCodeTwentyOneInverseVSourcePhase (q : Q) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base) (toAdd q.base) +
    qBeta (toAdd q.base) (toAdd y555NortonVQ.base)

/-- The full integer inverse packet coefficient retains both V phases and the U central phase. -/
def monsterNortonCodeTwentyOneInverseCoefficient (e : Fin 64) : ℤ :=
  nortonUIntegerSign
    (monsterNortonCodeTwentyOneInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 8 0)) *
  monsterNortonOctadInverseCoefficient e 0 *
  nortonUIntegerSign
    (monsterNortonCodeTwentyOneInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 8 e)) *
  nortonUIntegerSign (monsterNortonRemainingOctadUPhase 8 e) *
  nortonUIntegerSign
    (monsterNortonCodeTwentyOneInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 8 e))

/-- All complete integer coefficients of the actual inverse-sixth packet. -/
def monsterNortonCodeTwentyOneInverseCoefficientCache : Fin 64 → ℤ :=
  ![1, -1, -1, -1, -1, -1, -1, 1,
    -1, -1, -1, 1, -1, 1, 1, 1,
    -1, -1, -1, 1, -1, 1, 1, 1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, -1, -1, 1, -1, 1, 1, 1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    1, 1, 1, -1, 1, -1, -1, -1]

set_option maxHeartbeats 16000000 in
-- Verify every actual V polar and U central phase before using the finite packet cache.
/-- The full actual inverse coefficient is exactly its cached integer, with every sign retained. -/
theorem monsterNortonCodeTwentyOneInverseCoefficient_cache (e : Fin 64) :
    monsterNortonCodeTwentyOneInverseCoefficient e =
        monsterNortonCodeTwentyOneInverseCoefficientCache e := by
  revert e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

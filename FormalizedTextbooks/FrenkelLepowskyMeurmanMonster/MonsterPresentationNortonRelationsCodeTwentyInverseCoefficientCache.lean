/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual phase cache for the code-twenty inverse-sixth packet coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyMixedCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual V polar phase evaluated directly on a complete original source Q lift. -/
def monsterNortonCodeTwentyInverseVSourcePhase (q : Q) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base) (toAdd q.base) +
    qBeta (toAdd q.base) (toAdd y555NortonVQ.base)

/-- The full integer inverse packet coefficient retains both V phases and the U central phase. -/
def monsterNortonCodeTwentyInverseCoefficient (e : Fin 64) : ℤ :=
  nortonUIntegerSign
    (monsterNortonCodeTwentyInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 7 0)) *
  monsterNortonOctadInverseCoefficient e 0 *
  nortonUIntegerSign
    (monsterNortonCodeTwentyInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 7 e)) *
  nortonUIntegerSign (monsterNortonRemainingOctadUPhase 7 e) *
  nortonUIntegerSign
    (monsterNortonCodeTwentyInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 7 e))

/-- All complete integer coefficients of the actual inverse-sixth packet. -/
def monsterNortonCodeTwentyInverseCoefficientCache : Fin 64 → ℤ :=
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
theorem monsterNortonCodeTwentyInverseCoefficient_cache (e : Fin 64) :
    monsterNortonCodeTwentyInverseCoefficient e =
        monsterNortonCodeTwentyInverseCoefficientCache e := by
  revert e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

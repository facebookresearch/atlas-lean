/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual phase cache for the code-nineteen inverse-sixth packet coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenMixedCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual V polar phase evaluated directly on a complete original source Q lift. -/
def monsterNortonCodeNineteenInverseVSourcePhase (q : Q) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base) (toAdd q.base) +
    qBeta (toAdd q.base) (toAdd y555NortonVQ.base)

/-- The full integer inverse packet coefficient retains both V phases and the U central phase. -/
def monsterNortonCodeNineteenInverseCoefficient (e : Fin 64) : ℤ :=
  nortonUIntegerSign
    (monsterNortonCodeNineteenInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 6 0)) *
  monsterNortonOctadInverseCoefficient e 0 *
  nortonUIntegerSign
    (monsterNortonCodeNineteenInverseVSourcePhase (monsterNortonRemainingOctadUInputQ 6 e)) *
  nortonUIntegerSign (monsterNortonRemainingOctadUPhase 6 e) *
  nortonUIntegerSign
    (monsterNortonCodeNineteenInverseVSourcePhase (monsterNortonRemainingOctadUOutputQ 6 e))

/-- All complete integer coefficients of the actual inverse-sixth packet. -/
def monsterNortonCodeNineteenInverseCoefficientCache : Fin 64 → ℤ :=
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
theorem monsterNortonCodeNineteenInverseCoefficient_cache (e : Fin 64) :
    monsterNortonCodeNineteenInverseCoefficient e =
        monsterNortonCodeNineteenInverseCoefficientCache e := by
  revert e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

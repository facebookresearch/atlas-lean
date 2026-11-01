/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite integer sixth-step coefficients for the second preferred line-word input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Certified integer numerator of each reached second-input short summand. -/
def monsterNortonSecondSixthInteger : Fin 64 → ℤ :=
  ![
    -1, -1, 1, 1, -1, -1, 1, 1,
    1, 1, -1, -1, 1, 1, -1, -1,
    1, 1, -1, -1, 1, 1, -1, -1,
    -1, -1, 1, 1, -1, -1, 1, 1,
    1, 1, -1, -1, 1, 1, -1, -1,
    -1, -1, 1, 1, -1, -1, 1, 1,
    -1, -1, 1, 1, -1, -1, 1, 1,
    1, 1, -1, -1, 1, 1, -1, -1
  ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all sixty-four integers against the actual finite input and transported output phases.
/-- The displayed table equals the exact full sixth-step scalar numerator. -/
theorem monsterNortonSecondSixthInteger_actual (e : Fin 64) :
    monsterNortonEvenShortSixthInteger 1 e = monsterNortonSecondSixthInteger e := by
  revert e
  decide +kernel

/-- This finite integer table is the full real coefficient in the literal second-input packet. -/
theorem monsterNortonSecondSixthCoefficient_integer (e : Fin 64) :
    monsterNortonEvenShortSecondSixthCoefficient e =
      (monsterNortonSecondSixthInteger e : ℝ) / 8 := by
  change monsterNortonEvenShortSixthCoefficient 1 e = _
  rw [monsterNortonEvenShortSixthInteger_actual, monsterNortonSecondSixthInteger_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

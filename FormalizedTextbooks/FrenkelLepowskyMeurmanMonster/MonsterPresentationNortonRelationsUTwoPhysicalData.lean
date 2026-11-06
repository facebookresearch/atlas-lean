/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact denominator-four physical matrix for the literal squared Norton Leech action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUPhysicalTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Integer numerator of the genuine physical squared-U matrix, with denominator four. -/
def monsterNortonUTwoPhysicalNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
  ![-1, 0, 0, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 0, 0, 1, 1, 0, 1, 0, -1, -1, 0, 0],
  ![-1, 0, 0, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 0, 0, -1, 1, 0, 1, 0, 1, 1, 0, 0],
  ![1, 0, 0, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 0, 0, -1, -1, 0, 1, 0, -1, 1, 0, 0],
  ![1, 0, 0, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 0, 0, -1, -1, 0, 1, 0, -1, 1, 0, 0],
  ![1, 0, 0, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 0, 0, -1, 1, 0, 1, 0, -1, -1, 0, 0],
  ![1, 0, 0, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0],
  ![0, -1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1],
  ![0, 3, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1],
  ![-1, 0, 0, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 0, 0, -1, 1, 0, 1, 0, 1, 1, 0, 0],
  ![-1, 0, 0, -1, -1, 1, -1, 1, -1, -1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, -1, -1, 0, 0],
  ![1, 0, 0, -1, 1, 1, -1, 1, -1, 1, -1, -1, -1, 0, 0, 1, -1, 0, 1, 0, 1, -1, 0, 0],
  ![1, 0, 0, -1, -1, -1, 1, -1, 1, -1, 1, 1, -1, 0, 0, 1, -1, 0, 1, 0, 1, -1, 0, 0],
  ![1, 0, 0, 1, 1, 1, -1, -1, 1, -1, 1, -1, -1, 0, 0, -1, 1, 0, 1, 0, -1, -1, 0, 0],
  ![1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0],
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 3, 0, -1, 0, 0, -1, -1],
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, 3, 0, 0, -1, -1],
  ![-1, 0, 0, 1, -1, 1, -1, -1, 1, 1, -1, 1, 1, 0, 0, -1, -1, 0, 1, 0, 1, -1, 0, 0],
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, 3, -1],
  ![-1, 0, 0, 1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 0, 0, 1, -1, 0, 1, 0, -1, 1, 0, 0],
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 3, 0, 0, -1, 0, -1, 0, 0, -1, -1],
  ![-1, 0, 0, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, 0, 0, -1, -1, 0, 1, 0, 1, -1, 0, 0],
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, 3],
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1],
  ![-1, 0, 0, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, 0, 0, 1, -1, 0, 1, 0, -1, 1, 0, 0]]

set_option maxHeartbeats 4000000 in
-- Check all 576 entries of the true physical matrix product.
/-- The displayed matrix is exactly the square of the certified actual U numerator. -/
theorem monsterNortonUTwoPhysicalNumerator_certificate :
    monsterNortonUNumerator1 * monsterNortonUNumerator1 =
      4 • monsterNortonUTwoPhysicalNumerator := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

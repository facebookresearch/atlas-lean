/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integral basis action and fixed-point inverse for the Norton lattice word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The exact action on the actual integral lattice basis. -/
def monsterNortonUIntegral : Matrix (Fin 24) (Fin 24) ℤ :=
![
  ![-1, 0, 0, 3, 0, 3, 0, 4, -2, -2, 1, 2, -3, 0, 0, 4, -4, 4, 5, 4, -3, 0, -12, 3],
  ![0, 0, 0, -1, 0, -1, 0, -1, 1, 0, -1, -1, 0, 0, 0, -2, 1, -1, -1, -1, 1, 0, 2, -1],
  ![0, 0, 0, -1, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1, 1, -1, -1, 0, 0, 0, 2, -1],
  ![0, 0, 0, -1, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, -2, -1, 0, 0, 2, -1],
  ![0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 1, 0, 0, -1, 1, -1, -1, -1, 1, 0, 3, -1],
  ![-1, 0, -1, -1, 0, -1, 0, 0, 0, -1, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 3, -1],
  ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, -1, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0, 3, 0],
  ![1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, -1, 1],
  ![-1, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 2, -1],
  ![-1, -1, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0, -1, -1, 0, 1, 0, 2, -1],
  ![1, 0, 0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, -1, -1, 0, 0, 2, 0],
  ![1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1],
  ![1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1, 1, -1, -1, -1, 1, 0, 2, 0],
  ![1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2, 0, -1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
  ![1, 0, 0, 0, 0, 0, 0, -1, 1, 1, 1, 0, 1, 0, 0, 0, 1, -1, 0, -1, 0, 0, 2, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
  ![-1, 0, 0, 0, -1, 0, 0, 1, 0, -1, -1, 0, -1, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 0],
  ![-1, -1, -1, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, 0, -1, 0, 0, 0, -1, -1, -1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
  ![-1, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 1, -1, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0]
]

/-- A left inverse to the integral binary action minus the identity. -/
def monsterNortonUFixedPointInverse : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
![
  ![1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1],
  ![0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0],
  ![1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1],
  ![1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
  ![1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
  ![0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1],
  ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1],
  ![1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1],
  ![1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1],
  ![1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1],
  ![0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0],
  ![0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0],
  ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0],
  ![0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1],
  ![0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0],
  ![1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0],
  ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0],
  ![0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0],
  ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]
]

set_option maxHeartbeats 30000000 in
-- Check all 576 entries against the actual integral lattice basis.
/-- The displayed basis action follows from the actual physical numerator. -/
theorem monsterNortonU_integral_certificate :
    monsterNortonUNumerator1 * leechBasisMatrix =
      (4 : ℤ) • (leechBasisMatrix * monsterNortonUIntegral) := by
  decide +kernel

set_option maxHeartbeats 30000000 in
-- Check all 576 entries of a left inverse over the two-element field.
/-- The integral binary action has no nonzero fixed vector. -/
theorem monsterNortonU_fixed_point_certificate :
    monsterNortonUFixedPointInverse *
      (monsterNortonUIntegral.map (Int.castRingHom (ZMod 2)) - 1) = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

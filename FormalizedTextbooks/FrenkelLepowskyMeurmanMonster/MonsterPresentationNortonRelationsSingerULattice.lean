/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact physical matrix certificates for the Singer normalizer of Norton U. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLattice
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Four times the third power of the actual Norton physical matrix. -/
def monsterNortonSingerUCubeNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
![
  ![-1, -1, 1, -1, -1, -1, -1, 1,
    -1, 1, -1, -1, 0, 0, 0, 0,
    1, -1, 1, 1, 0, 0, 0, 0],
  ![-1, -1, -1, 1, 1, -1, 1, 1,
    1, 1, -1, 1, 0, 0, 0, 0,
    1, 1, -1, 1, 0, 0, 0, 0],
  ![1, 1, 1, -1, -1, 1, -1, -1,
    1, 1, -1, 1, 0, 0, 0, 0,
    1, 1, -1, 1, 0, 0, 0, 0],
  ![1, 1, 1, -1, 1, -1, 1, 1,
    -1, -1, 1, -1, 0, 0, 0, 0,
    1, 1, -1, 1, 0, 0, 0, 0],
  ![1, -1, 1, 1, 1, 1, -1, 1,
    1, 1, 1, -1, 0, 0, 0, 0,
    -1, -1, -1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, -3, -1, -1, -1,
    0, 0, 0, 0, 1, -1, -1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, -1, -1, -1,
    0, 0, 0, 0, -3, -1, -1, -1],
  ![1, -1, -1, -1, 1, -1, -1, -1,
    1, -1, -1, -1, 0, 0, 0, 0,
    -1, 1, 1, 1, 0, 0, 0, 0],
  ![-1, -1, -1, 1, -1, 1, -1, -1,
    -1, -1, 1, -1, 0, 0, 0, 0,
    1, 1, -1, 1, 0, 0, 0, 0],
  ![1, 1, -1, 1, -1, -1, -1, 1,
    1, -1, 1, 1, 0, 0, 0, 0,
    1, -1, 1, 1, 0, 0, 0, 0],
  ![-1, -1, 1, -1, 1, 1, 1, -1,
    1, -1, 1, 1, 0, 0, 0, 0,
    1, -1, 1, 1, 0, 0, 0, 0],
  ![1, 1, -1, 1, 1, 1, 1, -1,
    -1, 1, -1, -1, 0, 0, 0, 0,
    1, -1, 1, 1, 0, 0, 0, 0],
  ![-1, 1, -1, -1, -1, -1, 1, -1,
    1, 1, 1, -1, 0, 0, 0, 0,
    -1, -1, -1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, -1, -1, 3,
    0, 0, 0, 0, 1, -1, -1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, -1, -1, -1,
    0, 0, 0, 0, 1, -1, -1, 3],
  ![-1, 1, 1, 1, -1, 1, 1, 1,
    1, -1, -1, -1, 0, 0, 0, 0,
    -1, 1, 1, 1, 0, 0, 0, 0],
  ![-1, 1, -1, -1, 1, 1, -1, 1,
    -1, -1, -1, 1, 0, 0, 0, 0,
    -1, -1, -1, 1, 0, 0, 0, 0],
  ![-1, 1, 1, 1, 1, -1, -1, -1,
    -1, 1, 1, 1, 0, 0, 0, 0,
    -1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, -1, 3, -1,
    0, 0, 0, 0, 1, -1, -1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, -1, -1, -1,
    0, 0, 0, 0, 1, 3, -1, -1],
  ![1, -1, 1, 1, -1, -1, 1, -1,
    -1, -1, -1, 1, 0, 0, 0, 0,
    -1, -1, -1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, -1, -1, -1,
    0, 0, 0, 0, 1, -1, 3, -1],
  ![1, -1, -1, -1, -1, 1, 1, 1,
    -1, 1, 1, 1, 0, 0, 0, 0,
    -1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 3, -1, -1,
    0, 0, 0, 0, 1, -1, -1, -1]
]

set_option maxHeartbeats 8000000 in
-- Check the integer product giving the exact cubic numerator.
/-- The cubic numerator is certified against the actual first and second numerators. -/
theorem monsterNortonSingerUCube_certificate :
    monsterNortonUNumerator1 * monsterNortonUNumerator2 =
      (4 : ℤ) • monsterNortonSingerUCubeNumerator := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Compare the complete two physical permutation products over the integers.
/-- The exact physical permutation intertwines the first and cubic numerators. -/
theorem monsterNortonSingerUPhysical_certificate :
    monsterNortonSingerPhysicalMatrix * monsterNortonUNumerator1 =
      monsterNortonSingerUCubeNumerator * monsterNortonSingerPhysicalMatrix := by
  decide +kernel

private theorem quarter_mul (A B C : Matrix (Fin 24) (Fin 24) ℤ)
    (h : A * B = (4 : ℤ) • C) :
    ((1 / 4 : ℚ) • A.map (Int.castRingHom ℚ)) *
      ((1 / 4 : ℚ) • B.map (Int.castRingHom ℚ)) =
        (1 / 4 : ℚ) • C.map (Int.castRingHom ℚ) := by
  rw [smul_mul_assoc, mul_smul_comm, ← Matrix.map_mul, h]
  ext i j
  change (1 / 4 : ℚ) * ((1 / 4 : ℚ) * ((4 : ℤ) * C i j : ℤ)) =
    (1 / 4 : ℚ) * (C i j : ℚ)
  push_cast
  ring

/-- The certified cubic numerator is the third power of the actual rational matrix. -/
theorem monsterNortonSingerUMatrixQ_three : monsterNortonUMatrixQ ^ 3 =
    (1 / 4 : ℚ) • monsterNortonSingerUCubeNumerator.map (Int.castRingHom ℚ) := by
  calc
    _ = monsterNortonUMatrixQ * monsterNortonUMatrixQ ^ 2 := by noncomm_ring
    _ = _ := by
      rw [monsterNortonUMatrixQ_two]
      exact quarter_mul _ _ _ monsterNortonSingerUCube_certificate

/-- The actual rational physical matrices satisfy the Singer intertwining relation. -/
theorem monsterNortonSingerU_matrix_intertwines :
    monsterNortonSingerPhysicalMatrix.map (Int.castRingHom ℚ) * monsterNortonUMatrixQ =
      monsterNortonUMatrixQ ^ 3 *
        monsterNortonSingerPhysicalMatrix.map (Int.castRingHom ℚ) := by
  rw [monsterNortonSingerUMatrixQ_three, monsterNortonUMatrixQ,
    mul_smul_comm, smul_mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul,
    monsterNortonSingerUPhysical_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

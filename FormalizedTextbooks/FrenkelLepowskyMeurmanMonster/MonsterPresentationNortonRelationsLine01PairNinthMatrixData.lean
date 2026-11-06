/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact physical matrix after the ninth first-pair operator and its forward-U binding. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthPartners

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every true physical matrix numerator after the ninth operator, including all zeros. -/
def monsterNortonLine01PairNinthMatrixNumerator : Fin 24 → Fin 24 → ℤ :=
  ![![-1, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, -1, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, -1, 1, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0],
    ![0, -1, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![0, 1, 0, 0, 0, -1, 1, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0],
    ![0, 1, 0, 0, 0, -1, 1, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0],
    ![0, -1, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0],
    ![-1, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, -1, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![-1, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, -1, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![-1, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, -1, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, -1, 1, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check every physical entry from the full 240-source signed-pair contribution.
/-- The original diagonal and all signed pair images give precisely this full ninth matrix. -/
theorem monsterNortonLine01PairNinthMatrixNumerator_certificate (i j : Fin 24) :
    2 * (if i = j then monsterNortonLine01PairEighthDiagonalNumerator i else 0) +
      (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
        monsterNortonLine01PairEighthCoefficient k *
          (if monsterNortonLine01PairEighthPairFamily k = 0 then (1 : ℤ) else -1) *
          ((if i = monsterNortonLine01PairEighthPairFirst k ∧
              j = monsterNortonLine01PairEighthPairSecond k then (1 : ℤ) else 0) +
            (if i = monsterNortonLine01PairEighthPairSecond k ∧
              j = monsterNortonLine01PairEighthPairFirst k then (1 : ℤ) else 0))
        else 0) = 2 * monsterNortonLine01PairNinthMatrixNumerator i j := by
  revert i j
  decide +kernel

set_option maxRecDepth 10000 in
/-- Every ninth matrix entry is minus one half of the actual U image of the first pair matrix. -/
theorem monsterNortonLine01PairNinthMatrixU_certificate (i j : Fin 24) :
    monsterNortonUNumerator1 i 0 * monsterNortonUNumerator1 j 1 +
      monsterNortonUNumerator1 i 1 * monsterNortonUNumerator1 j 0 =
        -2 * monsterNortonLine01PairNinthMatrixNumerator i j := by
  revert i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

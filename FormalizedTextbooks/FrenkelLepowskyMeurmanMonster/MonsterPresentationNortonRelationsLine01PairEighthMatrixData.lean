/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer physical matrix data after the eighth first-pair operator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairAdjacentIndices

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every physical entry numerator of the eighth matrix, including the zeros. -/
def monsterNortonLine01PairEighthMatrixNumerator : Fin 24 → Fin 24 → ℤ :=
  ![![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The actual transported pair numerator uses precisely the displayed original coordinates. -/
theorem monsterNortonLine01PairInverseUPairNumerator (e : Fin 64) (i j : Fin 24) :
    monsterNortonUPairMatrixNumerator (monsterNortonLine01PairInversePhysicalPair e) i j =
      monsterNortonUNumerator1 i (monsterNortonLine01PairInversePairFirst e) *
        monsterNortonUNumerator1 j (monsterNortonLine01PairInversePairSecond e) +
      monsterNortonUNumerator1 i (monsterNortonLine01PairInversePairSecond e) *
        monsterNortonUNumerator1 j (monsterNortonLine01PairInversePairFirst e) := by
  unfold monsterNortonUPairMatrixNumerator monsterNortonLine01PairInversePhysicalPair
  rw [griessPairIndex_coordinates]
  simp only [monsterNortonLine01PairInversePair_increasing, ite_true]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check all 576 scalar outputs of the sixty-four-term source-column sum.
/-- All 576 finite matrix outputs agree with the actual integer transported source columns. -/
theorem monsterNortonLine01PairEighthMatrixNumerator_certificate (i j : Fin 24) :
    (∑ e : Fin 64, if monsterNortonLine01PairInverseIsPair e then
      monsterNortonLine01PairSixthNumerator e *
        (monsterNortonUNumerator1 i (monsterNortonLine01PairInversePairFirst e) *
          monsterNortonUNumerator1 j (monsterNortonLine01PairInversePairSecond e) +
        monsterNortonUNumerator1 i (monsterNortonLine01PairInversePairSecond e) *
          monsterNortonUNumerator1 j (monsterNortonLine01PairInversePairFirst e)) else 0) =
      16 * monsterNortonLine01PairEighthMatrixNumerator i j := by
  revert i j
  decide +kernel

/-- The full actual eighth physical matrix has these exact denominator-sixteen coordinates. -/
theorem monsterNortonLine01PairEighth_matrix_coordinates (i j : Fin 24) :
    monsterNortonMatrixProjection (y555NortonActualU.val monsterNortonLine01PairAfterSeventh)
      i j = (monsterNortonLine01PairEighthMatrixNumerator i j : ℝ) / 16 := by
  rw [monsterNortonLine01PairEighth_matrix]
  simp only [monsterNortonLine01PairInverseUPairNumerator]
  rw [monsterNortonLine01PairEighthMatrixNumerator_certificate, Int.cast_mul,
    Int.cast_ofNat]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

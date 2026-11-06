/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual full Norton U action on original pure off-diagonal symmetric matrices. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MatrixPairAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonLocalWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUTensorData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original pure A basis vector has the entire local matrix-only image. -/
theorem monsterNortonLocal_pair_matrix (f : localFiberSubgroup) (p : Fin 276) :
    localGriessRepresentation f (trialityABCBasis 0 p) =
      griessConwayDecode (conwayMatrixAction f.val.2 (trialityPairMatrix p), (0, 0)) := by
  have h := localGriessRepresentation_encode f (trialityABCBasis 0 p)
  rw [griessConwayEncode_ABC_zero_sparse, localConwayRawRepresentation_apply,
    map_zero, map_zero] at h
  change griessConwayEncode (localGriessRepresentation f (trialityABCBasis 0 p)) =
    (conwayMatrixAction f.val.2 (trialityPairMatrix p), (0, 0)) at h
  have hd := congrArg griessConwayDecode h
  rw [griessConwayDecode_encode] at hd
  exact hd

/-- Literal source U has this full Griess action on every physical A basis vector. -/
theorem monsterNortonU_pair_matrix (p : Fin 276) :
    y555NortonActualU.val (trialityABCBasis 0 p) =
      griessConwayDecode
        (conwayMatrixAction monsterNortonUFiber.val.2 (trialityPairMatrix p), (0, 0)) := by
  rw [← monsterNortonULocal_generated]
  exact monsterNortonLocal_pair_matrix monsterNortonUFiber p

/-- The exact denominator-sixteen integer numerator of that actual matrix image. -/
def monsterNortonUPairMatrixNumerator (p : Fin 276) (i j : Fin 24) : ℤ :=
  monsterNortonUNumerator1 i (griessCoordinatePair p).1 *
      monsterNortonUNumerator1 j (griessCoordinatePair p).2 +
    monsterNortonUNumerator1 i (griessCoordinatePair p).2 *
      monsterNortonUNumerator1 j (griessCoordinatePair p).1

/-- Every physical matrix entry follows from the actual two transported basis columns. -/
theorem monsterNortonUPairMatrix_coordinates (p : Fin 276) (i j : Fin 24) :
    conwayMatrixAction monsterNortonUFiber.val.2 (trialityPairMatrix p) i j =
      (monsterNortonUPairMatrixNumerator p i j : ℝ) / 16 := by
  rw [trialityPairMatrix, map_add, conwayMatrixAction_vecMulVec, conwayMatrixAction_vecMulVec]
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, monsterNortonUPhysicalMatrix_basis,
    monsterNortonUPairMatrixNumerator, Int.cast_add, Int.cast_mul]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

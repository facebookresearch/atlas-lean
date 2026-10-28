/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full literal squared Norton action on the original pure pair matrices. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoPhysicalCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem fiber_square_leech (f : localFiberSubgroup) :
    (f ^ 2).val.2 = f.val.2 ^ 2 := rfl

private theorem generated_fiber_apply (f : localFiberSubgroup) (x : GriessSpace) :
    (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f)).val x =
      localGriessRepresentation f x := rfl

/-- The literal squared source U has the entire matrix-only action on every physical A basis. -/
theorem monsterNortonUTwo_pair_matrix (p : Fin 276) :
    (y555NortonActualU ^ 2).val (trialityABCBasis 0 p) =
      griessConwayDecode
        (conwayMatrixAction (monsterNortonUFiber.val.2 ^ 2) (trialityPairMatrix p), (0, 0)) := by
  have h := monsterNortonLocal_pair_matrix (monsterNortonUFiber ^ 2) p
  have hg : localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup
      (monsterNortonUFiber ^ 2)) = y555NortonActualU ^ 2 := by
    simpa only [zpow_ofNat] using monsterNortonUFiber_generated_zpow (2 : ℤ)
  rw [← generated_fiber_apply, hg, fiber_square_leech] at h
  exact h

/-- Every actual Q element fixes every whole physical pair matrix. -/
theorem monsterNortonQ_pair_matrix (q : Q) (p : Fin 276) :
    (qIntoGenerated q).val (trialityABCBasis 0 p) = trialityABCBasis 0 p := by
  have h := monsterNortonLocal_pair_matrix (localFiberIncl q) p
  change (qIntoGenerated q).val (trialityABCBasis 0 p) =
    griessConwayDecode (conwayMatrixAction 1 (trialityPairMatrix p), (0, 0)) at h
  rw [map_one] at h
  change (qIntoGenerated q).val (trialityABCBasis 0 p) =
    griessConwayDecode (trialityPairMatrix p, (0, 0)) at h
  rw [← griessConwayEncode_ABC_zero_sparse, griessConwayDecode_encode] at h
  exact h

/-- Exact denominator-sixteen numerator of the squared physical pair-matrix transport. -/
def monsterNortonUTwoPairMatrixNumerator (p : Fin 276) (i j : Fin 24) : ℤ :=
  monsterNortonUTwoPhysicalNumerator i (griessCoordinatePair p).1 *
      monsterNortonUTwoPhysicalNumerator j (griessCoordinatePair p).2 +
    monsterNortonUTwoPhysicalNumerator i (griessCoordinatePair p).2 *
      monsterNortonUTwoPhysicalNumerator j (griessCoordinatePair p).1

/-- Every entry follows from the two complete actual squared physical columns. -/
theorem monsterNortonUTwoPairMatrix_coordinates (p : Fin 276) (i j : Fin 24) :
    conwayMatrixAction (monsterNortonUFiber.val.2 ^ 2) (trialityPairMatrix p) i j =
      (monsterNortonUTwoPairMatrixNumerator p i j : ℝ) / 16 := by
  rw [trialityPairMatrix, map_add, conwayMatrixAction_vecMulVec, conwayMatrixAction_vecMulVec]
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, monsterNortonUTwoPhysical_basis,
    monsterNortonUTwoPairMatrixNumerator, Int.cast_add, Int.cast_mul]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact actual V action on the original first-pair A,B,C dictionary. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEleventh

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A B dictionary vector is the difference of the two original signed-pair units. -/
theorem monsterNortonPairShort_B (p : Fin 276) :
    trialityABCBasis 1 p = monsterNortonPureShort (Sum.inl (0, p)) -
      monsterNortonPureShort (Sum.inl (1, p)) := by
  rw [monsterNortonPairShort_ABC, monsterNortonPairShort_ABC]
  simp only [ite_true, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
  module

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the two true pair phases using the actual physical shortest-vector dictionary.
/-- The two original first-pair families have the exact literal V polar phases one and zero. -/
theorem monsterNortonLine01PairV_phase (s : Fin 2) :
    qBeta (toAdd y555NortonVQ.base)
      (toAdd (monsterNortonShortQ (Sum.inl (s, monsterNortonLine01AdjacentPair 0))).base) +
    qBeta (toAdd (monsterNortonShortQ (Sum.inl (s, monsterNortonLine01AdjacentPair 0))).base)
      (toAdd y555NortonVQ.base) = if s = 0 then 1 else 0 := by
  rw [monsterNortonVBinaryCoordinates_actual]
  unfold monsterNortonShortQ
  simp only [griessShortIntegral, monsterNortonLine01AdjacentPair_coordinates]
  revert s
  decide +kernel

private def rawShortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] ConwayRawSpace where
  toFun X := (0, (X, 0))
  map_add' X Y := by simp only [Prod.mk_add_mk, zero_add]
  map_smul' c X := by simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp rawShortLift

private theorem shortLift_apply (X : GriessShortIndex → ℝ) :
    shortLift X = griessConwayDecode (0, (X, 0)) := by
  change griessConwayDecodeLinear (0, (X, 0)) = griessConwayDecode (0, (X, 0))
  rfl

/-- Literal V has the entire original signed-pair unit actions specified by those phases. -/
theorem monsterNortonLine01PairV_unit (s : Fin 2) :
    y555NortonV.val (monsterNortonPureShort (Sum.inl (s, monsterNortonLine01AdjacentPair 0))) =
      qSign (if s = 0 then 1 else 0) •
        monsterNortonPureShort (Sum.inl (s, monsterNortonLine01AdjacentPair 0)) := by
  rw [y555NortonV, monsterNortonPureShort]
  change localGriessRepresentation (localFiberIncl y555NortonVQ)
    (griessConwayDecode (0, (Pi.single _ 1, 0))) = _
  have hc : spinConjugation (localFiberIncl y555NortonVQ).val.1
      (monsterNortonShortQ (Sum.inl (s, monsterNortonLine01AdjacentPair 0))) =
      qCentral (if s = 0 then 1 else 0) *
        monsterNortonShortQ (Sum.inl (s, monsterNortonLine01AdjacentPair 0)) := by
    change spinConjugation (spinHolomorphIncl y555NortonVQ) _ = _
    rw [spinConjugation_incl, q_conjugation_central_phase, monsterNortonLine01PairV_phase]
  have h := monsterNortonGriessShortBasis_of_Q_image (localFiberIncl y555NortonVQ)
    (Sum.inl (s, monsterNortonLine01AdjacentPair 0))
    (Sum.inl (s, monsterNortonLine01AdjacentPair 0)) (if s = 0 then 1 else 0) hc
  have hs := h.trans (shortLift.map_smul (qSign (if s = 0 then 1 else 0))
    (Pi.single (Sum.inl (s, monsterNortonLine01AdjacentPair 0)) 1))
  simpa only [shortLift_apply] using hs

/-- V fixes the whole original first-pair A vector pointwise. -/
theorem monsterNortonLine01PairV_A :
    y555NortonV.val (trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0)) =
      trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0) := by
  have h : trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0) =
      griessConwayDecode (trialityPairMatrix (monsterNortonLine01AdjacentPair 0), (0, 0)) := by
    rw [← griessConwayEncode_ABC_zero_sparse, griessConwayDecode_encode]
  rw [h, y555NortonV]
  exact monsterNortonQ_matrix_fixed y555NortonVQ _ (trialityPairMatrix_symmetric _)

/-- V sends the entire original first-pair C vector to minus its B vector. -/
theorem monsterNortonLine01PairV_C :
    y555NortonV.val (trialityABCBasis 2 (monsterNortonLine01AdjacentPair 0)) =
      -trialityABCBasis 1 (monsterNortonLine01AdjacentPair 0) := by
  rw [monsterNortonPairShort_C, map_add, monsterNortonLine01PairV_unit,
    monsterNortonLine01PairV_unit, monsterNortonPairShort_B]
  simp only [ite_true, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), qSign_one, qSign_zero,
    neg_one_smul, one_smul]
  abel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

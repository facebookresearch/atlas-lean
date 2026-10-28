/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual V signs on the two surviving octad units and its exact pure-matrix action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsVBinaryCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
private theorem survivorFields (a : Fin 2) :
    monsterNortonLine01PairEighthIsPair ⟨8 * a.val, by omega⟩ ≠ true ∧
    monsterNortonLine01PairEighthOctadSlot ⟨8 * a.val, by omega⟩ = a ∧
    monsterNortonLine01PairEighthOctadSign ⟨8 * a.val, by omega⟩ =
      monsterNortonLine01PairNinthOctadTarget a := by
  revert a
  decide +kernel

/-- The surviving octad units are the actual U images of the two first-pair families. -/
theorem monsterNortonLine01PairSurvivor_output (a : Fin 2) :
    monsterNortonLine01PairEighthShortOutput ⟨8 * a.val, by omega⟩ =
      Sum.inr (Sum.inl (monsterNortonLine01PairEighthBlockOctad a,
        monsterNortonLine01PairNinthOctadTarget a)) := by
  obtain ⟨hp, ha, hr⟩ := survivorFields a
  unfold monsterNortonLine01PairEighthShortOutput monsterNortonLine01PairEighthBlockOctad
  rw [ite_eq_right hp]
  have hd := congrArg (fun b : Fin 2 => monsterNortonOctadIndex
    (monsterNortonLine01PairEighthOctadCodes b)
    (monsterNortonLine01PairEighthOctad_weight b)) ha
  exact congrArg (fun p : Fin 759 × Fin 64 =>
    (Sum.inr (Sum.inl p) : GriessShortIndex)) (Prod.ext hd hr)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check both actual polar phases after transporting the source shortest-vector dictionary.
/-- Literal V negates both surviving original octad units with its true Q polar phase. -/
theorem monsterNortonLine01PairTenthV_phase (a : Fin 2) :
    qBeta (toAdd y555NortonVQ.base)
      (toAdd (monsterNortonShortQ (monsterNortonLine01PairEighthShortOutput
        ⟨8 * a.val, by omega⟩)).base) +
    qBeta (toAdd (monsterNortonShortQ (monsterNortonLine01PairEighthShortOutput
      ⟨8 * a.val, by omega⟩)).base) (toAdd y555NortonVQ.base) = 1 := by
  rw [monsterNortonVBinaryCoordinates_actual]
  unfold monsterNortonShortQ
  rw [monsterNortonLine01PairEighthOutputIntegral_actual]
  revert a
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

/-- Literal V has the full genuine negative action on each surviving octad Griess unit. -/
theorem monsterNortonLine01PairTenthV_unit (a : Fin 2) :
    y555NortonV.val (monsterNortonPureShort
      (Sum.inr (Sum.inl (monsterNortonLine01PairEighthBlockOctad a,
        monsterNortonLine01PairNinthOctadTarget a)))) =
      -monsterNortonPureShort
        (Sum.inr (Sum.inl (monsterNortonLine01PairEighthBlockOctad a,
          monsterNortonLine01PairNinthOctadTarget a))) := by
  rw [← monsterNortonLine01PairSurvivor_output a]
  rw [y555NortonV, monsterNortonPureShort]
  change localGriessRepresentation (localFiberIncl y555NortonVQ)
    (griessConwayDecode (0, (Pi.single _ 1, 0))) = _
  have hc : spinConjugation (localFiberIncl y555NortonVQ).val.1
      (monsterNortonShortQ (monsterNortonLine01PairEighthShortOutput ⟨8 * a.val, by omega⟩)) =
      qCentral 1 * monsterNortonShortQ
        (monsterNortonLine01PairEighthShortOutput ⟨8 * a.val, by omega⟩) := by
    change spinConjugation (spinHolomorphIncl y555NortonVQ) _ = _
    rw [spinConjugation_incl, q_conjugation_central_phase, monsterNortonLine01PairTenthV_phase]
  have h := monsterNortonGriessShortBasis_of_Q_image (localFiberIncl y555NortonVQ)
    (monsterNortonLine01PairEighthShortOutput ⟨8 * a.val, by omega⟩)
    (monsterNortonLine01PairEighthShortOutput ⟨8 * a.val, by omega⟩) 1 hc
  have h' := h.trans (shortLift.map_smul (qSign 1)
    (Pi.single (monsterNortonLine01PairEighthShortOutput ⟨8 * a.val, by omega⟩) 1))
  simpa only [qSign_one, neg_one_smul, shortLift_apply] using h'

/-- Every actual Q element fixes every genuine pure symmetric matrix vector pointwise. -/
theorem monsterNortonQ_matrix_fixed (q : Q) (A : Matrix (Fin 24) (Fin 24) ℝ)
    (hA : ∀ i j, A i j = A j i) :
    localGriessRepresentation (localFiberIncl q) (griessConwayDecode (A, (0, 0))) =
      griessConwayDecode (A, (0, 0)) := by
  have h := localGriessRepresentation_encode (localFiberIncl q)
    (griessConwayDecode (A, (0, 0)))
  rw [griessConwayEncode_decode _ hA, localConwayRawRepresentation_apply,
    map_zero, map_zero] at h
  change griessConwayEncode (localGriessRepresentation (localFiberIncl q)
    (griessConwayDecode (A, (0, 0)))) = (conwayMatrixAction 1 A, (0, 0)) at h
  rw [map_one] at h
  have hd := congrArg griessConwayDecode h
  rw [griessConwayDecode_encode] at hd
  exact hd

/-- V fixes the entire actual forward-U image of the first physical pair matrix. -/
theorem monsterNortonLine01PairTenthV_matrix :
    y555NortonV.val (y555NortonActualU.val
      (trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0))) =
      y555NortonActualU.val (trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0)) := by
  rw [monsterNortonU_pair_matrix, y555NortonV]
  exact monsterNortonQ_matrix_fixed y555NortonVQ _
    (conwayMatrixAction_symmetric _ _ (trialityPairMatrix_symmetric _))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

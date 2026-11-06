/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual Q action on scaled short coordinates and integer-spin rank-one tensors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQShortDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegralVector

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))

private theorem short_smul (r : GriessShortIndex) (c : ℝ) :
    griessConwayDecode (0, (c • Pi.single r 1, 0)) =
      c • griessConwayDecode (0, (Pi.single r 1, 0)) :=
  shortLift.map_smul c (Pi.single r 1)

/-- The full actual Q action on a scaled short unit retains the genuine polar sign. -/
theorem monsterNortonQ_scaled_short (q : Q) (r : GriessShortIndex) (c : ℝ) :
    (qIntoGenerated q).val (griessConwayDecode (0, (c • Pi.single r 1, 0))) =
      griessConwayDecode (0,
        (((c * qSign (qBeta (toAdd q.base) (toAdd (monsterNortonShortQ r).base) +
          qBeta (toAdd (monsterNortonShortQ r).base) (toAdd q.base))) : ℝ) •
            Pi.single r 1, 0)) := by
  have hq : (qIntoGenerated q).val (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0,
        (qSign (qBeta (toAdd q.base) (toAdd (monsterNortonShortQ r).base) +
          qBeta (toAdd (monsterNortonShortQ r).base) (toAdd q.base)) • Pi.single r 1, 0)) :=
    monsterNortonQ_griess_short_basis q r
  rw [short_smul, map_smul, hq, short_smul, smul_smul, short_smul]

/-- Q acts on every integer-spin rank-one tensor by its full actual integer spin operator. -/
theorem monsterNortonQ_integer_rank_one (q : Q) (v : NortonUIntegerVector)
    (b : Fin 24 → ℝ) :
    (qIntoGenerated q).val (monsterNortonTensorLift
      (conwayTensorCoordinates (nortonUIntegerEmbed v ⊗ₜ[ℝ] b))) =
      monsterNortonTensorLift (conwayTensorCoordinates
        (nortonUIntegerEmbed (nortonUIntegerQ q v) ⊗ₜ[ℝ] b)) := by
  change localGriessRepresentation (localFiberIncl q)
    (monsterNortonTensorLift (conwayTensorCoordinates (nortonUIntegerEmbed v ⊗ₜ[ℝ] b))) = _
  rw [monsterNortonLocal_tensor_product_actual]
  change monsterNortonTensorLift (conwayTensorCoordinates
    (spinRepresentation q (nortonUIntegerEmbed v) ⊗ₜ[ℝ] b)) = _
  rw [nortonUIntegerQ_embed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact full tensor transport by actual Q elements, including the literal Norton v. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSparseTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualLocalCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual Q element applies its genuine spin operator to each physical tensor column. -/
theorem monsterNortonQ_tensor_coordinates (q : Q) (T : SpinIndex → Fin 24 → ℝ) :
    (qIntoGenerated q).val (monsterNortonTensorLift T) =
      monsterNortonTensorLift (fun t i => spinOperator q (fun u => T u i) t) := by
  change localGriessRepresentation (localFiberIncl q) (monsterNortonTensorLift T) = _
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [monsterNortonTensorLift_apply, localGriessRepresentation_encode,
    griessConwayEncode_decode _ (by intros; rfl), monsterNortonTensorLift_apply,
    griessConwayEncode_decode _ (by intros; rfl), localConwayRawRepresentation_apply]
  simp only [map_zero]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext t i
  exact localFiberQ_tensor_columns q T t i

/-- The literal Norton involution has this entire tensor action with its true central phase. -/
theorem monsterNortonV_tensor_coordinates (T : SpinIndex → Fin 24 → ℝ) :
    y555NortonV.val (monsterNortonTensorLift T) =
      monsterNortonTensorLift (fun t i => spinOperator y555NortonVQ (fun u => T u i) t) := by
  rw [y555NortonV]
  exact monsterNortonQ_tensor_coordinates y555NortonVQ T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

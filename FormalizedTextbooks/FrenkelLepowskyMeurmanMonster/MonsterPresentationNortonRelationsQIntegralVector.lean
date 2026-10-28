/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole actual integer tensor transport by Q and the literal Norton involution. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegralVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every actual Q element transports an integer pure tensor with its full integer spin action. -/
theorem monsterNortonQIntegralVector_actual (q : Q) (v : NortonUIntegerVector)
    (z : Fin 24 → ℤ) :
    (qIntoGenerated q).val (monsterNortonIntegralTensorVector v z) =
      monsterNortonIntegralTensorVector (nortonUIntegerQ q v) z := by
  change localGriessRepresentation (localFiberIncl q)
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed v ⊗ₜ[ℝ] leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)))) = _
  rw [monsterNortonLocal_tensor_product_actual]
  change monsterNortonTensorLift (conwayTensorCoordinates
    ((spinRepresentation q (nortonUIntegerEmbed v)) ⊗ₜ[ℝ]
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))) = _
  rw [nortonUIntegerQ_embed]
  rfl

/-- The entire actual Norton v action preserves the Leech factor and retains every spin sign. -/
theorem monsterNortonVIntegralVector_actual (v : NortonUIntegerVector) (z : Fin 24 → ℤ) :
    y555NortonV.val (monsterNortonIntegralTensorVector v z) =
      monsterNortonIntegralTensorVector (nortonUIntegerQ y555NortonVQ v) z := by
  rw [y555NortonV]
  exact monsterNortonQIntegralVector_actual y555NortonVQ v z

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

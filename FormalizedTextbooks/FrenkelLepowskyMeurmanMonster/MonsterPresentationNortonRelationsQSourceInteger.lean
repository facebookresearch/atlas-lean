/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact inverse Norton tensor transport after the actual Q action on source Y. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSourceInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegralVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegerBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

private theorem integer_source_Y (d : Fin 2048) :
    nortonUIntegerEmbed (monsterNortonSourceYInteger d) =
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) -
        Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 := by
  have h : nortonUIntegerEmbed (monsterNortonSourceYInteger d) =
      nortonUIntegerEmbed (Pi.single ⟨d.val, by omega⟩ 1) -
        nortonUIntegerEmbed (Pi.single ⟨d.val + 2048, by omega⟩ 1) := by
    ext t
    simp [monsterNortonSourceYInteger, nortonUIntegerEmbed]
  rw [h, monsterNortonUIntegerEmbed_single, monsterNortonUIntegerEmbed_single]

/-- Q transports a source Y spin vector by its complete actual integral operator. -/
theorem monsterNortonQ_source_Y_integer (q : Q) (d : Fin 2048) (j : Fin 24) :
    spinOperator q (trialityYSpin d j) =
      ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) / Real.sqrt 2) •
        nortonUIntegerEmbed (nortonUIntegerQ q (monsterNortonSourceYInteger d)) := by
  rw [monsterNortonSourceYSpin_basis, ← integer_source_Y]
  change spinRepresentation q (_ • _) = _
  rw [map_smul, nortonUIntegerQ_embed]

/-- The inverse literal Norton word has its full actual spin and Leech tensor-column action. -/
theorem monsterNortonU_inverse_tensor_column (a : SpinSpace) (j : Fin 24) :
    (y555NortonActualU⁻¹).val (monsterNortonTensorLift (conwaySpinColumn a j)) =
      monsterNortonTensorLift (conwayTensorCoordinates
        ((monsterNortonUFiber.val.1⁻¹).val a ⊗ₜ[ℝ]
          (monsterNortonUFiber.val.2⁻¹).val (Pi.single j 1))) := by
  have hc : conwaySpinColumn a j =
      conwayTensorCoordinates (a ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)) := by
    ext t i
    simp [conwayTensorCoordinates_tmul, conwaySpinColumn, Pi.single_apply]
  rw [hc, ← monsterNortonULocal_generated, ← map_inv]
  change localGriessRepresentation (monsterNortonUFiber⁻¹)
    (monsterNortonTensorLift (conwayTensorCoordinates
      (a ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)))) = _
  exact monsterNortonLocal_tensor_product_actual _ _ _

/-- Inverse Norton after any genuine Q action has one exact signed integer Gaussian numerator. -/
theorem monsterNortonU_inverse_Q_source_Y (q : Q) (d : Fin 2048) (j : Fin 24) :
    (y555NortonActualU⁻¹).val
      ((qIntoGenerated q).val (trialityXYZBasis 1 (finProdFinEquiv (d, j)))) =
      (((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) /
        Real.sqrt 2) * (-1 / 8 : ℝ)) •
          monsterNortonTensorLift (conwayTensorCoordinates
            (nortonUIntegerEmbed (monsterNortonUCompactInverseNumerator
              (nortonUIntegerQ q (monsterNortonSourceYInteger d))) ⊗ₜ[ℝ]
                (monsterNortonUFiber.val.2⁻¹).val (Pi.single j 1))) := by
  rw [monsterNortonQ_source_Y, monsterNortonU_inverse_tensor_column,
    monsterNortonQ_source_Y_integer, map_smul,
    monsterNortonUCompactInverseSpin_actual_embed, smul_smul,
    ← TensorProduct.smul_tmul', map_smul, map_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

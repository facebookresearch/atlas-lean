/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact inverse Norton tensor transport after actual Q on source Z. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSourceZQCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceInteger

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- Its real embedding is exactly the sum of the original low and high spin-dictionary deltas. -/
theorem monsterNortonSourceZInteger_embed (d : Fin 2048) :
    nortonUIntegerEmbed (monsterNortonSourceZInteger d) =
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) +
        Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 := by
  have h : nortonUIntegerEmbed (monsterNortonSourceZInteger d) =
      nortonUIntegerEmbed (Pi.single ⟨d.val, by omega⟩ 1) +
        nortonUIntegerEmbed (Pi.single ⟨d.val + 2048, by omega⟩ 1) := by
    ext t
    simp [monsterNortonSourceZInteger, nortonUIntegerEmbed]
  rw [h, monsterNortonUIntegerEmbed_single, monsterNortonUIntegerEmbed_single]

/-- Actual Q transports Z by its complete integral spin action and original weight sign. -/
theorem monsterNortonQ_source_Z_integer (q : Q) (d : Fin 2048) :
    spinOperator q (trialityZSpin d) =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) / Real.sqrt 2) •
        nortonUIntegerEmbed (nortonUIntegerQ q (monsterNortonSourceZInteger d)) := by
  rw [monsterNortonSourceZSpin_basis, ← monsterNortonSourceZInteger_embed]
  change spinRepresentation q (_ • _) = _
  rw [map_smul, nortonUIntegerQ_embed]

/-- The entire inverse-U image after any actual Q on Z has the exact Gaussian integer numerator. -/
theorem monsterNortonU_inverse_Q_source_Z (q : Q) (d : Fin 2048) (j : Fin 24) :
    (y555NortonActualU⁻¹).val
      ((qIntoGenerated q).val (trialityXYZBasis 2 (finProdFinEquiv (d, j)))) =
      ((qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) /
        Real.sqrt 2) * (-1 / 8 : ℝ)) •
          monsterNortonTensorLift (conwayTensorCoordinates
            (nortonUIntegerEmbed (monsterNortonUCompactInverseNumerator
              (nortonUIntegerQ q (monsterNortonSourceZInteger d))) ⊗ₜ[ℝ]
                (monsterNortonUFiber.val.2⁻¹).val (Pi.single j 1))) := by
  rw [monsterNortonQ_source_Z, monsterNortonU_inverse_tensor_column,
    monsterNortonQ_source_Z_integer, map_smul,
    monsterNortonUCompactInverseSpin_actual_embed, smul_smul,
    ← TensorProduct.smul_tmul', map_smul, map_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

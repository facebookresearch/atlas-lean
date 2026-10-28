/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact two-delta actual Q images of the source Z tensor columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A source Z vector is exactly its genuine physical spin column. -/
theorem monsterNortonSourceZ_tensor_column (d : Fin 2048) (j : Fin 24) :
    trialityXYZBasis 2 (finProdFinEquiv (d, j)) =
      monsterNortonTensorLift (conwaySpinColumn (trialityZSpin d) j) := by
  calc
    _ = griessConwayDecode (griessConwayEncode
      (trialityXYZBasis 2 (finProdFinEquiv (d, j)))) := (griessConwayDecode_encode _).symm
    _ = _ := by rw [griessConwayEncode_Z_basis, trialityZTensor_column]; rfl

/-- Every actual Q element applies its genuine spin action to a source Z column. -/
theorem monsterNortonQ_source_Z (q : Q) (d : Fin 2048) (j : Fin 24) :
    (qIntoGenerated q).val (trialityXYZBasis 2 (finProdFinEquiv (d, j))) =
      monsterNortonTensorLift (conwaySpinColumn (spinOperator q (trialityZSpin d)) j) := by
  rw [monsterNortonSourceZ_tensor_column, monsterNortonQ_tensor_coordinates]
  apply congrArg monsterNortonTensorLift
  ext t i
  by_cases hi : i = j
  · subst i
    simp [conwaySpinColumn]
  · simp [spinOperator, conwaySpinColumn, hi]

/-- Both translated physical delta labels and full central phases in the Q image of Z. -/
noncomputable def monsterNortonSourceZQSpinImage (q : Q) (d : Fin 2048) : SpinSpace :=
  (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) / Real.sqrt 2) •
    (qSign (toAdd q.coeff + spinDot (spinModulation q)
      (golayLabelCoefficients ⟨d.val, by omega⟩ + spinTranslation q)) •
        (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩ + spinTranslation q) 1 : SpinSpace) +
      qSign (toAdd q.coeff + spinDot (spinModulation q)
        (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + spinTranslation q)) •
          (Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + spinTranslation q) 1 :
            SpinSpace))

/-- The finite two-delta formula follows from the actual source spin representation. -/
theorem monsterNortonSourceZQSpinImage_actual (q : Q) (d : Fin 2048) :
    spinOperator q (trialityZSpin d) = monsterNortonSourceZQSpinImage q d := by
  rw [monsterNortonSourceZSpin_basis]
  change spinRepresentation q (_ • (_ + _)) = _
  rw [map_smul, map_add]
  change _ • (spinOperator q _ + spinOperator q _) = _
  rw [monsterNortonQ_spin_delta, monsterNortonQ_spin_delta]
  rfl

/-- The entire actual Q image of Z is the stated two translated spin-delta columns. -/
theorem monsterNortonQ_source_Z_explicit (q : Q) (d : Fin 2048) (j : Fin 24) :
    (qIntoGenerated q).val (trialityXYZBasis 2 (finProdFinEquiv (d, j))) =
      monsterNortonTensorLift (conwaySpinColumn (monsterNortonSourceZQSpinImage q d) j) := by
  rw [monsterNortonQ_source_Z, monsterNortonSourceZQSpinImage_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

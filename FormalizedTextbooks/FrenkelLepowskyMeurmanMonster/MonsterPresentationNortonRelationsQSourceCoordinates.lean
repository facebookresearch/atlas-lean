/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual Q action on the source X and Y dictionary vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQShortDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQTensorBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A source X vector is exactly its genuine odd-short coordinate vector. -/
theorem monsterNortonSourceX_pure_short (d : Fin 2048) (j : Fin 24) :
    trialityXYZBasis 0 (finProdFinEquiv (d, j)) =
      monsterNortonPureShort (Sum.inr (Sum.inr (d, j))) := by
  calc
    _ = griessConwayDecode (griessConwayEncode
      (trialityXYZBasis 0 (finProdFinEquiv (d, j)))) := (griessConwayDecode_encode _).symm
    _ = _ := by rw [griessConwayEncode_X_basis]; rfl

/-- A source Y vector is exactly its genuine physical spin column. -/
theorem monsterNortonSourceY_tensor_column (d : Fin 2048) (j : Fin 24) :
    trialityXYZBasis 1 (finProdFinEquiv (d, j)) =
      monsterNortonTensorLift (conwaySpinColumn (trialityYSpin d j) j) := by
  calc
    _ = griessConwayDecode (griessConwayEncode
      (trialityXYZBasis 1 (finProdFinEquiv (d, j)))) := (griessConwayDecode_encode _).symm
    _ = _ := by rw [griessConwayEncode_Y_basis, trialityYTensor_column]; rfl

/-- The exact polar sign governing Q on the source odd-short vector. -/
noncomputable def monsterNortonSourceXQPhase (q : Q) (d : Fin 2048) (j : Fin 24) :
    ZMod 2 :=
  qBeta (toAdd q.base) (toAdd (monsterNortonShortQ (Sum.inr (Sum.inr (d, j)))).base) +
    qBeta (toAdd (monsterNortonShortQ (Sum.inr (Sum.inr (d, j)))).base) (toAdd q.base)

/-- Every actual Q element acts on source X with its true central polar sign. -/
theorem monsterNortonQ_source_X (q : Q) (d : Fin 2048) (j : Fin 24) :
    (qIntoGenerated q).val (trialityXYZBasis 0 (finProdFinEquiv (d, j))) =
      qSign (monsterNortonSourceXQPhase q d j) •
        trialityXYZBasis 0 (finProdFinEquiv (d, j)) := by
  rw [monsterNortonSourceX_pure_short]
  change localGriessRepresentation (localFiberIncl q)
    (griessConwayDecode (0, (Pi.single (Sum.inr (Sum.inr (d, j))) 1, 0))) = _
  rw [monsterNortonQ_griess_short_basis]
  change griessConwayDecodeLinear (0,
    (qSign (monsterNortonSourceXQPhase q d j) • Pi.single (Sum.inr (Sum.inr (d, j))) 1, 0)) =
      qSign (monsterNortonSourceXQPhase q d j) •
        griessConwayDecodeLinear (0, (Pi.single (Sum.inr (Sum.inr (d, j))) 1, 0))
  have h : ((0, (qSign (monsterNortonSourceXQPhase q d j) •
      (Pi.single (Sum.inr (Sum.inr (d, j))) 1 : GriessShortIndex → ℝ), 0)) : ConwayRawSpace) =
      qSign (monsterNortonSourceXQPhase q d j) •
        (0, ((Pi.single (Sum.inr (Sum.inr (d, j))) 1 : GriessShortIndex → ℝ), 0)) := by
    simp only [Prod.smul_mk, smul_zero]
  rw [h, map_smul]

/-- Every actual Q element applies its genuine spin action to a source Y column. -/
theorem monsterNortonQ_source_Y (q : Q) (d : Fin 2048) (j : Fin 24) :
    (qIntoGenerated q).val (trialityXYZBasis 1 (finProdFinEquiv (d, j))) =
      monsterNortonTensorLift (conwaySpinColumn (spinOperator q (trialityYSpin d j)) j) := by
  rw [monsterNortonSourceY_tensor_column, monsterNortonQ_tensor_coordinates]
  apply congrArg monsterNortonTensorLift
  ext t i
  by_cases hi : i = j
  · subst i
    simp [conwaySpinColumn]
  · simp [spinOperator, conwaySpinColumn, hi]

/-- The two translated delta columns giving the exact Q image of a source Y spin vector. -/
noncomputable def monsterNortonSourceYQSpinImage (q : Q) (d : Fin 2048) (j : Fin 24) :
    SpinSpace :=
  ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) / Real.sqrt 2) •
    (qSign (toAdd q.coeff + spinDot (spinModulation q)
      (golayLabelCoefficients ⟨d.val, by omega⟩ + spinTranslation q)) •
        (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩ + spinTranslation q) 1 : SpinSpace) -
      qSign (toAdd q.coeff + spinDot (spinModulation q)
        (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + spinTranslation q)) •
          (Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + spinTranslation q) 1 :
            SpinSpace))

/-- Both translated labels and both central signs follow from the actual Q spin action. -/
theorem monsterNortonSourceYQSpinImage_actual (q : Q) (d : Fin 2048) (j : Fin 24) :
    spinOperator q (trialityYSpin d j) = monsterNortonSourceYQSpinImage q d j := by
  rw [monsterNortonSourceYSpin_basis]
  change spinRepresentation q (_ • (_ - _)) = _
  rw [map_smul, map_sub]
  change _ • (spinOperator q _ - spinOperator q _) = _
  rw [monsterNortonQ_spin_delta, monsterNortonQ_spin_delta]
  rfl

/-- The complete actual source Y image is the displayed two translated delta columns. -/
theorem monsterNortonQ_source_Y_explicit (q : Q) (d : Fin 2048) (j : Fin 24) :
    (qIntoGenerated q).val (trialityXYZBasis 1 (finProdFinEquiv (d, j))) =
      monsterNortonTensorLift (conwaySpinColumn (monsterNortonSourceYQSpinImage q d j) j) := by
  rw [monsterNortonQ_source_Y, monsterNortonSourceYQSpinImage_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

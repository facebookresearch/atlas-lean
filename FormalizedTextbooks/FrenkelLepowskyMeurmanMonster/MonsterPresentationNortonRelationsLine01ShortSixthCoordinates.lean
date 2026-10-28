/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete actual short-coordinate state at the sixth first-line word step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSecondV
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Projection onto the genuine physical short-coordinate summand. -/
noncomputable def monsterNortonShortProjection : GriessSpace →ₗ[ℝ] (GriessShortIndex → ℝ) where
  toFun x := (griessConwayEncode x).2.1
  map_add' x y := congrArg (fun r : ConwayRawSpace => r.2.1)
    (griessConwayEncodeLinear.map_add x y)
  map_smul' c x := congrArg (fun r : ConwayRawSpace => r.2.1)
    (griessConwayEncodeLinear.map_smul c x)

/-- The original pure-short inclusion is a section of the physical short projection. -/
theorem monsterNortonShortProjection_short (X : GriessShortIndex → ℝ) :
    monsterNortonShortProjection (griessConwayDecode (0, (X, 0))) = X := by
  change (griessConwayEncode (griessConwayDecode (0, (X, 0)))).2.1 = X
  rw [griessConwayEncode_decode _ (by intros; rfl)]

/-- Actual tensor vectors have zero physical short coordinates. -/
theorem monsterNortonShortProjection_tensor (T : SpinIndex → Fin 24 → ℝ) :
    monsterNortonShortProjection (monsterNortonTensorLift T) = 0 := by
  change (griessConwayEncode (monsterNortonTensorLift T)).2.1 = 0
  rw [monsterNortonTensorLift_apply, griessConwayEncode_decode _ (by intros; rfl)]

/-- The full actual scalar on each transported short summand, retaining every Q phase. -/
noncomputable def monsterNortonLine01ShortSixthCoefficient (a : Fin 64) (i : Fin 24) : ℝ :=
  (qSign (golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a) 11) *
      (if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit i.val then -1
        else 1)) *
    qSign (monsterNortonSourceXQFinitePhase y555NortonVQ
      (monsterNortonLine01ShortInputCode a) i) *
    (qSign (monsterNortonLine01ShortInversePhase a (monsterNortonLine01ShortPhysicalSlot i)) *
      qSign (monsterNortonLine01ShortInverseVPhase a i))

/-- The reached source summand has exactly one signed actual short coordinate. -/
theorem monsterNortonLine01SourcePairAfterVInverseUV_short (a : Fin 64) (i : Fin 24) :
    monsterNortonShortProjection (monsterNortonLine01SourcePairAfterVInverseUV a i) =
      monsterNortonLine01ShortSixthCoefficient a i •
        Pi.single (monsterNortonLine01ShortInverseOutput a
          (monsterNortonLine01ShortPhysicalSlot i)) 1 := by
  rw [monsterNortonLine01SourcePairAfterVInverseUV, map_add, map_smul,
    monsterNortonShortProjection_short, map_smul, map_smul,
    monsterNortonShortProjection_tensor, smul_zero, smul_zero, add_zero, smul_smul]
  rfl

/-- The sixth full state has its exact signed finite short-coordinate expansion. -/
theorem monsterNortonLine01ShortSixth_coordinates :
    monsterNortonShortProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV =
      (1 / 64 : ℝ) • ∑ a : Fin 64,
        (monsterNortonLine01InitialSpinSigns a : ℝ) • ∑ i : Fin 24,
          (monsterNortonUNumerator1 i 0 : ℝ) •
            (monsterNortonLine01ShortSixthCoefficient a i •
              Pi.single (monsterNortonLine01ShortInverseOutput a
                (monsterNortonLine01ShortPhysicalSlot i)) 1) := by
  rw [monsterNortonLine01TensorAfterVUExtraInverseVInverseUV, map_smul, map_sum]
  simp only [map_smul, map_sum, monsterNortonLine01SourcePairAfterVInverseUV_short]

/-- Each actual octad coordinate at the seventh word step is its exact Fourier image. -/
theorem monsterNortonLine01ShortSeventh_octad_coordinates (d : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1
      (Sum.inr (Sum.inl (d, e))) =
      trialityOctadAction (fun r => monsterNortonShortProjection
        monsterNortonLine01TensorAfterVUExtraInverseVInverseUV (Sum.inr (Sum.inl (d, r)))) e :=
  monsterNortonTensor_extra_octad_coordinates _ d e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

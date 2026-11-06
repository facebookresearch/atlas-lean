/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual rank-one tensor column aggregation for the first Norton line word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactInput
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ColumnEnumeration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactInverseSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSecondV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The actual real tensor coordinate projection of the Griess space. -/
noncomputable def monsterNortonTensorProjection :
    GriessSpace →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) where
  toFun x := (griessConwayEncode x).2.2
  map_add' x y := congrArg (fun r : ConwayRawSpace => r.2.2)
    (griessConwayEncodeLinear.map_add x y)
  map_smul' c x := congrArg (fun r : ConwayRawSpace => r.2.2)
    (griessConwayEncodeLinear.map_smul c x)

/-- The true tensor inclusion is a section of the tensor projection. -/
theorem monsterNortonTensorProjection_lift (T : SpinIndex → Fin 24 → ℝ) :
    monsterNortonTensorProjection (monsterNortonTensorLift T) = T := by
  change (griessConwayEncode (monsterNortonTensorLift T)).2.2 = T
  rw [monsterNortonTensorLift_apply, griessConwayEncode_decode _ (by intros; rfl)]

/-- A pure actual short vector has zero tensor projection. -/
theorem monsterNortonTensorProjection_short (X : GriessShortIndex → ℝ) :
    monsterNortonTensorProjection (griessConwayDecode (0, (X, 0))) = 0 := by
  change (griessConwayEncode (griessConwayDecode (0, (X, 0)))).2.2 = 0
  rw [griessConwayEncode_decode _ (by intros; rfl)]

/-- The actual rank-one tensor inclusion has its literal physical tensor projection. -/
theorem monsterNortonTensorProjection_rank_one (b : Fin 24 → ℝ) (a : SpinSpace) :
    monsterNortonTensorProjection (monsterNortonTensorRankOne b a) =
      conwayTensorCoordinates (a ⊗ₜ[ℝ] b) := by
  change monsterNortonTensorProjection (monsterNortonTensorLift _) = _
  exact monsterNortonTensorProjection_lift _

/-- The exact integer vector in each supported physical column after inverse u and the next v. -/
def monsterNortonLine01CompactTensorSpin (k : Fin 16) : NortonUIntegerVector :=
  nortonUIntegerQ y555NortonVQ
    (monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector k))

/-- The column aggregate equals the full actual weighted source transport, including all phases. -/
theorem monsterNortonLine01CompactTensorSpin_sum (k : Fin 16) (b : Fin 24 → ℝ) :
    monsterNortonTensorRankOne b (nortonUIntegerEmbed (monsterNortonLine01CompactTensorSpin k)) =
      ∑ a : Fin 64, ((monsterNortonLine01InitialSpinSigns a *
        nortonUIntegerSign (golayMaskWeight
          (golayEncodedMask (monsterNortonLine01ShortInputCode a).val) / 4 : ℕ) *
        (if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit
          (monsterNortonLine01ShortPhysicalColumn k).val then -1 else 1) : ℤ) : ℝ) •
          monsterNortonTensorRankOne b (nortonUIntegerEmbed
            (nortonUIntegerQ y555NortonVQ (monsterNortonUCompactInverseNumerator
              (nortonUIntegerQ y555NortonVQ
                (monsterNortonSourceYInteger (monsterNortonLine01ShortInputCode a)))))) := by
  rw [monsterNortonLine01CompactTensorSpin, monsterNortonLine01CompactInputVector_actual,
    monsterNortonUCompactInverseNumerator_sum, monsterNortonUIntegerQ_sum,
    monsterNortonTensorRankOne_integer_sum]

/-- The reached source summand has precisely its displayed actual tensor projection. -/
theorem monsterNortonLine01SourcePairAfterVInverseUV_tensor (a : Fin 64) (i : Fin 24) :
    monsterNortonTensorProjection (monsterNortonLine01SourcePairAfterVInverseUV a i) =
      qSign (golayMaskWeight (golayEncodedMask (monsterNortonLine01ShortInputCode a).val) /
        4 : ℕ) •
        ((((if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit i.val then
          (-1 : ℝ) else 1) / Real.sqrt 2) * (-1 / 8 : ℝ)) •
          conwayTensorCoordinates
            (nortonUIntegerEmbed (nortonUIntegerQ y555NortonVQ
              (monsterNortonUCompactInverseNumerator (nortonUIntegerQ y555NortonVQ
                (monsterNortonSourceYInteger (monsterNortonLine01ShortInputCode a))))) ⊗ₜ[ℝ]
                  (monsterNortonUFiber.val.2⁻¹).val (Pi.single i 1))) := by
  rw [monsterNortonLine01SourcePairAfterVInverseUV, map_add, map_smul,
    monsterNortonTensorProjection_short, smul_zero, zero_add, map_smul, map_smul,
    monsterNortonTensorProjection_lift]

/-- The actual sixth tensor state is a sum of exactly sixteen transported integer columns. -/
theorem monsterNortonLine01TensorSixth_columns :
    monsterNortonTensorProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV =
      (-1 / (512 * Real.sqrt 2) : ℝ) • ∑ k : Fin 16,
        (monsterNortonUNumerator1 (monsterNortonLine01ShortPhysicalColumn k) 0 : ℝ) •
          monsterNortonTensorProjection (monsterNortonTensorRankOne
            ((monsterNortonUFiber.val.2⁻¹).val
              (Pi.single (monsterNortonLine01ShortPhysicalColumn k) 1))
            (nortonUIntegerEmbed (monsterNortonLine01CompactTensorSpin k))) := by
  rw [monsterNortonLine01TensorAfterVUExtraInverseVInverseUV, map_smul, map_sum]
  simp only [map_smul, map_sum, monsterNortonLine01SourcePairAfterVInverseUV_tensor]
  simp_rw [monsterNortonLine01_supported_columns]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [monsterNortonLine01CompactTensorSpin_sum, map_sum]
  simp only [map_smul, Finset.smul_sum, monsterNortonTensorProjection_rank_one]
  apply Finset.sum_congr rfl
  intro a _
  simp only [smul_smul]
  congr 1
  simp only [Int.cast_mul, Int.cast_ite, Int.cast_neg, Int.cast_one,
    nortonUIntegerSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

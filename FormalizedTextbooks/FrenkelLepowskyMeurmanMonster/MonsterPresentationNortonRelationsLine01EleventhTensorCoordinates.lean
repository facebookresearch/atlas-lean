/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual eleventh tensor factorization in the original spin and physical coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhTensorCoefficientBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhTensorCoefficientBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhTensorCoefficientBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhTensorCoefficientBatch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhTensorSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every source tensor coefficient has the checked rank-one eleventh factorization. -/
theorem monsterNortonLine01EleventhTensor_source_coefficients
    (a : Fin 64) (h : Fin 2) (i : Fin 24) :
    monsterNortonLine01EleventhTensorIntegerNumerator
      ⟨(monsterNortonLine01ShortInputCode a).val + 2048 * h.val, by omega⟩ i =
        16 * monsterNortonLine01EleventhSpinVector
          ⟨(monsterNortonLine01ShortInputCode a).val + 2048 * h.val, by omega⟩ *
            monsterNortonUNumerator1 i 0 := by
  fin_cases i
  · exact monsterNortonLine01EleventhTensor_coefficient_batch0 a h 0
  · exact monsterNortonLine01EleventhTensor_coefficient_batch0 a h 1
  · exact monsterNortonLine01EleventhTensor_coefficient_batch0 a h 2
  · exact monsterNortonLine01EleventhTensor_coefficient_batch0 a h 3
  · exact monsterNortonLine01EleventhTensor_coefficient_batch0 a h 4
  · exact monsterNortonLine01EleventhTensor_coefficient_batch0 a h 5
  · exact monsterNortonLine01EleventhTensor_coefficient_batch1 a h 0
  · exact monsterNortonLine01EleventhTensor_coefficient_batch1 a h 1
  · exact monsterNortonLine01EleventhTensor_coefficient_batch1 a h 2
  · exact monsterNortonLine01EleventhTensor_coefficient_batch1 a h 3
  · exact monsterNortonLine01EleventhTensor_coefficient_batch1 a h 4
  · exact monsterNortonLine01EleventhTensor_coefficient_batch1 a h 5
  · exact monsterNortonLine01EleventhTensor_coefficient_batch2 a h 0
  · exact monsterNortonLine01EleventhTensor_coefficient_batch2 a h 1
  · exact monsterNortonLine01EleventhTensor_coefficient_batch2 a h 2
  · exact monsterNortonLine01EleventhTensor_coefficient_batch2 a h 3
  · exact monsterNortonLine01EleventhTensor_coefficient_batch2 a h 4
  · exact monsterNortonLine01EleventhTensor_coefficient_batch2 a h 5
  · exact monsterNortonLine01EleventhTensor_coefficient_batch3 a h 0
  · exact monsterNortonLine01EleventhTensor_coefficient_batch3 a h 1
  · exact monsterNortonLine01EleventhTensor_coefficient_batch3 a h 2
  · exact monsterNortonLine01EleventhTensor_coefficient_batch3 a h 3
  · exact monsterNortonLine01EleventhTensor_coefficient_batch3 a h 4
  · exact monsterNortonLine01EleventhTensor_coefficient_batch3 a h 5

/-- The rank-one eleventh factorization holds on all 4096 spin labels, including every zero. -/
theorem monsterNortonLine01EleventhTensorInteger_factorization (n : Fin 4096) (i : Fin 24) :
    monsterNortonLine01EleventhTensorIntegerNumerator n i =
      16 * monsterNortonLine01EleventhSpinVector n * monsterNortonUNumerator1 i 0 := by
  let d : Fin 2048 := ⟨n.val % 2048, by omega⟩
  by_cases hd : monsterNortonLine01SourceCodeSupport d
  · let a := monsterNortonLine01SourceCodeLookup d
    let h : Fin 2 := ⟨n.val / 2048, by omega⟩
    have hc : monsterNortonLine01ShortInputCode a = d := hd
    have he : (⟨(monsterNortonLine01ShortInputCode a).val + 2048 * h.val, by omega⟩ :
        Fin 4096) = n := by
      apply Fin.ext
      change (monsterNortonLine01ShortInputCode a).val + 2048 * (n.val / 2048) = n.val
      rw [congrArg Fin.val hc]
      exact Nat.mod_add_div n.val 2048
    have hr := monsterNortonLine01EleventhTensor_source_coefficients a h i
    rw [he] at hr
    exact hr
  · rw [monsterNortonLine01EleventhTensorInteger_source_zero n i hd,
      monsterNortonLine01EleventhSpinVector_source_zero n hd, mul_zero, zero_mul]

/-- Every actual eleventh tensor entry has the verified spin factor and actual Leech column. -/
theorem monsterNortonLine01EleventhTensor_factorization_actual (n : Fin 4096) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).2.2
        (golayLabelCoefficients n) i =
          (1 / (8 * Real.sqrt 2) : ℝ) * (monsterNortonLine01EleventhSpinVector n : ℝ) *
            monsterNortonUFiber.val.2.val (Pi.single 0 1) i := by
  rw [monsterNortonLine01EleventhTensorInteger_actual,
    monsterNortonLine01EleventhTensorInteger_factorization]
  simp only [Int.cast_mul, Int.cast_ofNat]
  rw [monsterNortonUPhysicalMatrix_basis]
  field_simp
  ring

/-- The genuine pure Griess tensor carrying the complete verified eleventh tensor state. -/
noncomputable def monsterNortonLine01EleventhTensorVector : GriessSpace :=
  (1 / (8 * Real.sqrt 2) : ℝ) •
    monsterNortonTensorRankOne (monsterNortonUFiber.val.2.val (Pi.single 0 1))
      (nortonUIntegerEmbed monsterNortonLine01EleventhSpinVector)

/-- The entire actual eleventh tensor projection equals this genuine rank-one tensor projection. -/
theorem monsterNortonLine01EleventhTensor_projection :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).2.2 =
        monsterNortonTensorProjection monsterNortonLine01EleventhTensorVector := by
  ext t i
  have h := monsterNortonLine01EleventhTensor_factorization_actual (nortonUIntegerLabel t) i
  rw [nortonUIntegerLabel_inverse] at h
  rw [monsterNortonLine01EleventhTensorVector, map_smul,
    monsterNortonTensorProjection_rank_one]
  simpa only [conwayTensorCoordinates_tmul, Pi.smul_apply, smul_eq_mul,
    nortonUIntegerEmbed, mul_assoc] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual triality sends a physical spin-delta tensor column through two source XYZ vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSourceSpin

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem two_delta (a b : ℝ) (ha : a * a = 1) (hb : b * b = 1)
    (u v : SpinSpace) :
    (1 / Real.sqrt 2 : ℝ) •
      (a • ((a / Real.sqrt 2) • (u - v)) +
        b • ((b / Real.sqrt 2) • (u + v))) = u := by
  have hr : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  ext t
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  linear_combination (u t - v t) * ha + (u t + v t) * hb - u t * hr

private theorem two_delta_high (a b : ℝ) (ha : a * a = 1) (hb : b * b = 1)
    (u v : SpinSpace) :
    (1 / Real.sqrt 2 : ℝ) •
      (-a • ((a / Real.sqrt 2) • (u - v)) +
        b • ((b / Real.sqrt 2) • (u + v))) = v := by
  have hr : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  ext t
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  linear_combination -(u t - v t) * ha + (u t + v t) * hb - v t * hr

private theorem source_spin_delta (d : Fin 2048) (j : Fin 24) :
    (1 / Real.sqrt 2 : ℝ) •
      ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) • trialityYSpin d j +
        qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) • trialityZSpin d) =
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) := by
  rw [monsterNortonSourceYSpin_basis, monsterNortonSourceZSpin_basis]
  apply two_delta
  · split_ifs <;> norm_num
  · exact qSign_sq _

private theorem source_spin_delta_high (d : Fin 2048) (j : Fin 24) :
    (1 / Real.sqrt 2 : ℝ) •
      (-(if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) • trialityYSpin d j +
        qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) • trialityZSpin d) =
      (Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 : SpinSpace) := by
  rw [monsterNortonSourceYSpin_basis, monsterNortonSourceZSpin_basis]
  apply two_delta_high
  · split_ifs <;> norm_num
  · exact qSign_sq _

/-- A pure physical tensor column over the low dictionary delta is a two-vector source word. -/
theorem monsterNortonTensorDeltaLow_source (d : Fin 2048) (j : Fin 24) :
    griessConwayDecode (0, (0, conwaySpinColumn
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) j)) =
      (1 / Real.sqrt 2 : ℝ) •
        ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) •
          trialityXYZBasis 1 (finProdFinEquiv (d,j)) +
          qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) •
            trialityXYZBasis 2 (finProdFinEquiv (d,j))) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode _ = griessConwayEncodeLinear _
  rw [map_smul, map_add, map_smul, map_smul]
  change griessConwayEncode _ = (1 / Real.sqrt 2 : ℝ) •
    ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) •
      griessConwayEncode (trialityXYZBasis 1 (finProdFinEquiv (d,j))) +
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) •
        griessConwayEncode (trialityXYZBasis 2 (finProdFinEquiv (d,j))))
  rw [griessConwayEncode_decode _ (by intro i k; rfl),
    griessConwayEncode_Y_basis, griessConwayEncode_Z_basis,
    trialityYTensor_column, trialityZTensor_column]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i k
    split_ifs <;> simp
  · ext r
    split_ifs <;> simp
  · ext t i
    have hs := congrFun (source_spin_delta d j) t
    by_cases h : i = j
    · subst i
      simpa only [conwaySpinColumn, ite_true, Prod.smul_mk, Prod.mk_add_mk,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hs.symm
    · split_ifs <;> simp [conwaySpinColumn, h]

/-- A pure physical tensor column over the high dictionary delta is a two-vector source word. -/
theorem monsterNortonTensorDeltaHigh_source (d : Fin 2048) (j : Fin 24) :
    griessConwayDecode (0, (0, conwaySpinColumn
      (Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 : SpinSpace) j)) =
      (1 / Real.sqrt 2 : ℝ) •
        (-(if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) •
          trialityXYZBasis 1 (finProdFinEquiv (d,j)) +
          qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) •
            trialityXYZBasis 2 (finProdFinEquiv (d,j))) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode _ = griessConwayEncodeLinear _
  rw [map_smul, map_add, map_smul, map_smul]
  change griessConwayEncode _ = (1 / Real.sqrt 2 : ℝ) •
    (-(if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) •
      griessConwayEncode (trialityXYZBasis 1 (finProdFinEquiv (d,j))) +
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) •
        griessConwayEncode (trialityXYZBasis 2 (finProdFinEquiv (d,j))))
  rw [griessConwayEncode_decode _ (by intro i k; rfl),
    griessConwayEncode_Y_basis, griessConwayEncode_Z_basis,
    trialityYTensor_column, trialityZTensor_column]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i k
    split_ifs <;> simp
  · ext r
    split_ifs <;> simp
  · ext t i
    have hs := congrFun (source_spin_delta_high d j) t
    by_cases h : i = j
    · subst i
      simpa only [conwaySpinColumn, ite_true, Prod.smul_mk, Prod.mk_add_mk,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hs.symm
    · split_ifs <;> simp [conwaySpinColumn, h]

/-- Actual extra sends this low delta column to the source Z and X vectors with exact phases. -/
theorem monsterNortonExtra_tensor_delta_low (d : Fin 2048) (j : Fin 24) :
    sExtra (griessConwayDecode (0, (0, conwaySpinColumn
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) j))) =
      (1 / Real.sqrt 2 : ℝ) •
        ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) •
          trialityXYZBasis 2 (finProdFinEquiv (d,j)) +
          qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) •
            trialityXYZBasis 0 (finProdFinEquiv (d,j))) := by
  rw [monsterNortonTensorDeltaLow_source, map_smul, map_add, map_smul, map_smul,
    sExtra_XYZ_basis, sExtra_XYZ_basis,
    show trialityCycle 1 = 2 by decide +kernel,
    show trialityCycle 2 = 0 by decide +kernel]

/-- Actual extra sends this high delta column to the source Z and X vectors with exact phases. -/
theorem monsterNortonExtra_tensor_delta_high (d : Fin 2048) (j : Fin 24) :
    sExtra (griessConwayDecode (0, (0, conwaySpinColumn
      (Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 : SpinSpace) j))) =
      (1 / Real.sqrt 2 : ℝ) •
        (-(if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) •
          trialityXYZBasis 2 (finProdFinEquiv (d,j)) +
          qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) •
            trialityXYZBasis 0 (finProdFinEquiv (d,j))) := by
  rw [monsterNortonTensorDeltaHigh_source, map_smul, map_add, map_smul, map_smul,
    sExtra_XYZ_basis, sExtra_XYZ_basis,
    show trialityCycle 1 = 2 by decide +kernel,
    show trialityCycle 2 = 0 by decide +kernel]

private theorem inverse_xyz (s : Fin 3) (k : Fin 49152) :
    sExtra.symm (trialityXYZBasis s k) = trialityXYZBasis (trialityCycle.symm s) k := by
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, sExtra_XYZ_basis, Equiv.apply_symm_apply]

/-- Actual inverse extra sends the low delta column to source X and Y with exact phases. -/
theorem monsterNortonExtraInverse_tensor_delta_low (d : Fin 2048) (j : Fin 24) :
    sExtra.symm (griessConwayDecode (0, (0, conwaySpinColumn
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) j))) =
      (1 / Real.sqrt 2 : ℝ) •
        ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) •
          trialityXYZBasis 0 (finProdFinEquiv (d,j)) +
          qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) •
            trialityXYZBasis 1 (finProdFinEquiv (d,j))) := by
  rw [monsterNortonTensorDeltaLow_source, map_smul, map_add, map_smul, map_smul,
    inverse_xyz, inverse_xyz,
    show trialityCycle.symm 1 = 0 by decide +kernel,
    show trialityCycle.symm 2 = 1 by decide +kernel]

/-- Actual inverse extra sends the high delta column to source X and Y with exact phases. -/
theorem monsterNortonExtraInverse_tensor_delta_high (d : Fin 2048) (j : Fin 24) :
    sExtra.symm (griessConwayDecode (0, (0, conwaySpinColumn
      (Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 : SpinSpace) j))) =
      (1 / Real.sqrt 2 : ℝ) •
        (-(if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) •
          trialityXYZBasis 0 (finProdFinEquiv (d,j)) +
          qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) •
            trialityXYZBasis 1 (finProdFinEquiv (d,j))) := by
  rw [monsterNortonTensorDeltaHigh_source, map_smul, map_add, map_smul, map_smul,
    inverse_xyz, inverse_xyz,
    show trialityCycle.symm 1 = 0 by decide +kernel,
    show trialityCycle.symm 2 = 1 by decide +kernel]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

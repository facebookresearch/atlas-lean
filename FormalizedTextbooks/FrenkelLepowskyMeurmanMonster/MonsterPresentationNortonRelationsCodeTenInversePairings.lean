/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual inverse packet pairings at every preferred-basis-ten candidate entry. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenInverseCoefficients

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem matrix_short (A : Matrix (Fin 24) (Fin 24) ℝ) (r : GriessShortIndex) :
    griessForm (griessConwayDecode
      (Matrix.diagonal (fun i => A i i), (monsterNortonMatrixTrialityShort A, 0)))
      (monsterNortonPureShort r) = monsterNortonMatrixTrialityShort A r := by
  rw [monsterNortonForm_pureShort_right]
  change (griessConwayEncode (griessConwayDecode _)).2.1 r = _
  rw [griessConwayEncode_decode _ (by
    intro i j
    simp only [Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h, Ne.symm])]

private theorem matrix_tensor (A : Matrix (Fin 24) (Fin 24) ℝ) (t : SpinIndex) (j : Fin 24) :
    griessForm (griessConwayDecode
      (Matrix.diagonal (fun i => A i i), (monsterNortonMatrixTrialityShort A, 0)))
      (monsterNortonTensorUnit t j) = 0 := by
  rw [monsterNortonForm_tensorUnit_right]
  rw [griessConwayEncode_decode _ (by
    intro i j
    simp only [Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h, Ne.symm])]
  rfl

/-- The whole sixth inverse packet is its physical matrix and its two actual odd source images. -/
theorem monsterNortonCodeTenInverse_source_expansion :
    monsterNortonEvenShortPairsInverseSixth 10 0 =
      (-1 / 2 : ℝ) • griessConwayDecode
        (Matrix.diagonal (fun i => monsterNortonEvenShortPairsUMatrix 10 i i),
          (monsterNortonMatrixTrialityShort (monsterNortonEvenShortPairsUMatrix 10), 0)) +
      (-1 / 2 : ℝ) • monsterNortonShortExtraPacket (Sum.inr (Sum.inr (338, 3))) +
      (-1 / 2 : ℝ) • monsterNortonShortExtraPacket (Sum.inr (Sum.inr (82, 3))) := by
  have hl : monsterNortonEvenShortFirstUOutput ⟨(10 : Fin 11).val, by omega⟩ =
      Sum.inr (Sum.inr (338, 3)) := rfl
  have hu : monsterNortonEvenShortUpperUOutput 10 = Sum.inr (Sum.inr (82, 3)) := rfl
  rw [monsterNortonEvenShortPairsInverseSixth, hl, hu,
    monsterNortonCodeTenInverseSourcePhases.1, monsterNortonCodeTenInverseSourcePhases.2]
  have hv : qSign (monsterNortonEvenShortInitialVPhase
      ⟨(10 : Fin 11).val, by omega⟩) = (-1 : ℝ) := by
    norm_num [monsterNortonEvenShortInitialVPhase, qSign]
  rw [hv]
  norm_num [monsterNortonPairFamilySign, smul_add, smul_smul]
  exact (add_assoc _ _ _).symm

/-- Every complete inverse short pairing equals its certified original pair coefficient. -/
theorem monsterNortonCodeTenInverseHalf_short_form (p : Fin 2 × Fin 128) :
    griessForm (monsterNortonEvenShortPairsInverseSixth 10 0)
      (monsterNortonPureShort (monsterNortonCodeTenInverseShortIndex p)) =
        (monsterNortonCodeTenInverseShortCoefficient p.1 p.2 : ℝ) / 32 := by
  rw [monsterNortonCodeTenInverse_source_expansion]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    matrix_short, monsterNortonOddExtra_short_form, mul_zero, add_zero]
  rw [monsterNortonCodeTenInverseShortIndex, monsterNortonMatrixTrialityShort]
  unfold monsterNortonEvenShortPairsUMatrix
  rw [monsterNortonUPairMatrix_coordinates]
  simp only [monsterNortonUPairMatrixNumerator, monsterNortonEvenShortPairIndex,
    monsterNortonCodeTenInversePair, griessPairIndex_coordinates,
    monsterNortonCodeTenInversePair_lt, monsterNortonEvenShortPairCoordinate_positive, ite_true]
  change (-1 / 2 : ℝ) *
    (if p.1 = 0 then
      ((monsterNortonUNumerator1 (monsterNortonCodeTenInversePairFirst p.2) 0 *
        monsterNortonUNumerator1 (monsterNortonCodeTenInversePairSecond p.2) 16 +
        monsterNortonUNumerator1 (monsterNortonCodeTenInversePairFirst p.2) 16 *
        monsterNortonUNumerator1 (monsterNortonCodeTenInversePairSecond p.2) 0 : ℤ) : ℝ) / 16
    else -(((monsterNortonUNumerator1 (monsterNortonCodeTenInversePairFirst p.2) 0 *
      monsterNortonUNumerator1 (monsterNortonCodeTenInversePairSecond p.2) 16 +
      monsterNortonUNumerator1 (monsterNortonCodeTenInversePairFirst p.2) 16 *
      monsterNortonUNumerator1 (monsterNortonCodeTenInversePairSecond p.2) 0 : ℤ) : ℝ) / 16)) = _
  have h := congrArg (fun z : ℤ => (z : ℝ)) (monsterNortonCodeTenInverseShortRead_coefficient p)
  simp only [monsterNortonCodeTenInverseShortRead, Int.cast_mul, Int.cast_ite,
    Int.cast_neg, Int.cast_one] at h
  split_ifs with hs <;> simp only [hs, ite_true, ite_false] at h ⊢ <;>
    push_cast at h ⊢ <;> linear_combination h / 32

private theorem sign_last (i : Fin 4) :
    qSign (golayLabelCoefficients (monsterNortonCodeTenInverseSpinLabel i) 11) =
      if (monsterNortonCodeTenInverseSpinLabel i).val < 2048 then (1 : ℝ) else -1 := by
  have h : ∀ i : Fin 4,
      golayLabelCoefficients (monsterNortonCodeTenInverseSpinLabel i) 11 =
        (if (monsterNortonCodeTenInverseSpinLabel i).val < 2048 then 0 else 1 : ZMod 2) := by
    decide +kernel
  rw [h]
  split_ifs <;> norm_num [qSign]

/-- Every complete inverse tensor pairing retains both actual odd columns and their signs. -/
theorem monsterNortonCodeTenInverseHalf_tensor_form (p : Fin 4 × Fin 1) :
    griessForm (monsterNortonEvenShortPairsInverseSixth 10 0)
      (monsterNortonTensorUnit (monsterNortonCodeTenInverseTensorIndex p).1
        (monsterNortonCodeTenInverseTensorIndex p).2) =
      (monsterNortonCodeTenInverseTensorCoefficient p : ℝ) / (32 * Real.sqrt 2) := by
  rw [monsterNortonCodeTenInverse_source_expansion]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    matrix_tensor, monsterNortonOddExtra_tensor_form, mul_zero, zero_add]
  simp only [monsterNortonCodeTenInverseTensorIndex, spinDictionaryCode,
    spinDictionaryLabel_coeff, sign_last]
  have hb : (golayEncodedMask 82).testBit 3 = false := by decide +kernel
  have hc : (golayEncodedMask 338).testBit 3 = true := by decide +kernel
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [monsterNortonCodeTenInverseTensorCoefficient,
      monsterNortonCodeTenInverseSpinCoefficient, monsterNortonCodeTenInverseLeech,
      monsterNortonCodeTenInverseColumns, monsterNortonCodeTenInverseSpinLabel, hb, hc] <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

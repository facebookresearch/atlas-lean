/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete actual second-half pairing, including its physical matrix contribution. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfNormGram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUWhole
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMatrixPacketPairing

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem form_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem form_sum_left {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → GriessSpace) (y : GriessSpace) :
    griessForm (∑ i, c i • v i) y = ∑ i, c i * griessForm (v i) y := by
  rw [form_symm, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_symm]

private theorem cast_product_sum {ι : Type*} [Fintype ι]
    (a b : ι → ℤ) (p q : ℝ) :
    (∑ i, (a i : ℝ) / p * ((b i : ℝ) / q)) =
      ((∑ i, a i * b i : ℤ) : ℝ) / (p * q) := by
  simp only [div_mul_div_comm, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_div]

private theorem matrix_symmetric (p : Fin 8) :
    ∀ i j, conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonSecondHalfPairIndex p)) i j =
        conwayMatrixAction monsterNortonUFiber.val.2
          (trialityPairMatrix (monsterNortonSecondHalfPairIndex p)) j i :=
  conwayMatrixAction_symmetric _ _ (trialityPairMatrix_symmetric _)

private theorem matrix_octad_zero (A : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, A i j = A j i) (d : Fin 759) (v : Fin 64 → ℝ) :
    griessForm (griessConwayDecode (A, (0, 0))) (monsterNortonOctadShortVector d v) = 0 := by
  unfold monsterNortonOctadShortVector
  rw [monsterNortonForm_pure_matrix_raw A 0 _ 0 ha (by intros; rfl)]
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

/-- Each entire actual transported A unit has the displayed exact inverse-half pairing. -/
theorem monsterNortonSecondHalfMatrixGram_actual (p : Fin 8) :
    griessForm (griessConwayDecode (conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonSecondHalfPairIndex p)), (0, 0)))
      monsterNortonEvenShortSecondInverseSixthPacket =
        ((-(∑ j : Fin 24, monsterNortonSecondHalfMatrixNumerator p j j *
          monsterNortonSecondSourceMatrixNumerator j j) : ℤ) : ℝ) / 512 := by
  unfold monsterNortonEvenShortSecondInverseSixthPacket
  simp only [map_add, map_smul, smul_eq_mul]
  have hm := monsterNortonForm_pure_matrix_diagonal
    (conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonSecondHalfPairIndex p)))
    (fun i => monsterNortonEvenShortSecondUMatrix i i)
    (monsterNortonMatrixTrialityShort monsterNortonEvenShortSecondUMatrix) (matrix_symmetric p)
  change _ * _ + _ * (_ + _) = _
  change (-1 / 2 : ℝ) * griessForm _
    (griessConwayDecode (Matrix.diagonal (fun i => monsterNortonEvenShortSecondUMatrix i i),
      (monsterNortonMatrixTrialityShort monsterNortonEvenShortSecondUMatrix, 0))) +
    (-1 / 2 : ℝ) * (griessForm _ (monsterNortonOctadShortVector _ _) +
      griessForm _ (monsterNortonOctadShortVector _ _)) = _
  rw [hm, matrix_octad_zero _ (matrix_symmetric p), matrix_octad_zero _ (matrix_symmetric p)]
  simp only [add_zero, mul_zero]
  simp_rw [monsterNortonSecondHalfMatrixNumerator_actual,
    monsterNortonSecondSourceMatrixNumerator_actual]
  rw [cast_product_sum]
  push_cast
  ring

private theorem short_coefficient (i : NortonSecondHalfShortIndex) :
    monsterNortonSecondHalfShortCoefficient i =
      (monsterNortonSecondHalfShortNumerator i : ℝ) / 16 := by
  rcases i with ⟨i, s⟩ | ⟨d, e⟩
  · norm_num [monsterNortonSecondHalfShortCoefficient, monsterNortonSecondHalfShortNumerator]
  · rfl

/-- The complete actual physical matrix packet contributes exactly one sixteenth. -/
theorem monsterNortonSecondHalfUMatrixPairing_actual :
    griessForm monsterNortonSecondHalfUMatrixPacket
      monsterNortonEvenShortSecondInverseSixthPacket = 1 / 16 := by
  rw [monsterNortonSecondHalfUMatrixPacket, form_sum_left]
  simp_rw [monsterNortonSecondHalfMatrixGram_actual]
  rw [cast_product_sum]
  have hi : (∑ p : Fin 8, monsterNortonSecondHalfPairCoefficient p *
      -(∑ j : Fin 24, monsterNortonSecondHalfMatrixNumerator p j j *
        monsterNortonSecondSourceMatrixNumerator j j)) = 512 := by
    simp only [mul_neg, Finset.sum_neg_distrib]
    exact monsterNortonSecondHalfMatrixPairing_integer
  rw [hi]
  norm_num

/-- The complete actual short packet contributes exactly fifteen sixteenths. -/
theorem monsterNortonSecondHalfUShortPairing_actual :
    griessForm monsterNortonSecondHalfUShortPacket
      monsterNortonEvenShortSecondInverseSixthPacket = 15 / 16 := by
  rw [monsterNortonSecondHalfUShortPacket, form_sum_left]
  simp_rw [short_coefficient, form_symm _ monsterNortonEvenShortSecondInverseSixthPacket,
    monsterNortonSecondHalfInverseShortGram_actual]
  rw [cast_product_sum, monsterNortonSecondHalfShortPairing_integer]
  norm_num

/-- The entire actual sparse U image has maximal pairing with the whole sixth inverse half. -/
theorem monsterNortonSecondHalfU_pairing_one :
    griessForm (y555NortonActualU.val monsterNortonSecondHalfPacket)
      monsterNortonEvenShortSecondInverseSixthPacket = 1 := by
  rw [monsterNortonSecondHalfUWhole_actual, map_add, LinearMap.add_apply,
    monsterNortonSecondHalfUMatrixPairing_actual, monsterNortonSecondHalfUShortPairing_actual]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

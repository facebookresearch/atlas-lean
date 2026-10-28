/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Maximal whole actual U pairing with the complete code-three inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadThreeInverseGram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUWhole

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem form_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem form_sum_left {I : Type*} [Fintype I]
    (c : I → ℝ) (v : I → GriessSpace) (y : GriessSpace) :
    griessForm (∑ i, c i • v i) y = ∑ i, c i * griessForm (v i) y := by
  rw [form_symm, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_symm]

private theorem cast_product_sum {I : Type*} [Fintype I]
    (a b : I → ℤ) (p q : ℝ) :
    (∑ i, (a i : ℝ) / p * ((b i : ℝ) / q)) =
      ((∑ i, a i * b i : ℤ) : ℝ) / (p * q) := by
  simp only [div_mul_div_comm, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_div]

/-- Full actual matrix-unit pairings with the entire integer-expanded inverse packet. -/
theorem monsterNortonOctadThreeReturnMatrixGram_actual (p : Fin 8) :
    griessForm (griessConwayDecode (conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonPairHalfPairIndex 11 p)), (0, 0)))
      monsterNortonOctadThreeInverseSixthPacket =
        ((∑ e : Fin 64, monsterNortonOctadThreeInverseIntegerCoefficient e *
          monsterNortonOctadThreeInverseMatrixGram p e : ℤ) : ℝ) / 128 := by
  rw [monsterNortonOctadThreeInverseSixthPacket_sum, map_sum]
  simp only [map_smul, smul_eq_mul, monsterNortonOctadThreeInverseMatrixGram_actual]
  rw [cast_product_sum]
  norm_num

/-- Full actual short-unit pairings with the entire integer-expanded inverse packet. -/
theorem monsterNortonOctadThreeReturnShortGram_actual (i : NortonPairHalfShortIndex) :
    griessForm monsterNortonOctadThreeInverseSixthPacket
      (monsterNortonPureShort (monsterNortonPairHalfUPoolOutput
        (monsterNortonPairHalfUPoolStorage 11 i))) =
        ((∑ e : Fin 64, monsterNortonOctadThreeInverseIntegerCoefficient e *
          monsterNortonOctadThreeInverseShortGram e i : ℤ) : ℝ) / 64 := by
  rw [monsterNortonOctadThreeInverseSixthPacket_sum, form_sum_left]
  simp_rw [monsterNortonOctadThreeInverseShortGram_actual]
  rw [cast_product_sum]
  norm_num

/-- The entire actual transported matrix packet contributes exactly one sixteenth. -/
theorem monsterNortonOctadThreeReturnUMatrix_actual :
    griessForm (monsterNortonPairHalfUMatrixPacket 11)
      monsterNortonOctadThreeInverseSixthPacket = 1 / 16 := by
  rw [monsterNortonPairHalfUMatrixPacket, form_sum_left]
  simp_rw [monsterNortonOctadThreeReturnMatrixGram_actual]
  rw [cast_product_sum, monsterNortonOctadThreeReturnMatrix_integer]
  norm_num

private theorem short_coefficient (i : NortonPairHalfShortIndex) :
    monsterNortonPairHalfShortCoefficient 11 i =
      (monsterNortonOctadThreeReturnShortNumerator i : ℝ) / 16 := by
  rcases i with ⟨p, s⟩ | ⟨d, e⟩ <;> rfl

/-- The entire actual transported short packet contributes exactly fifteen sixteenths. -/
theorem monsterNortonOctadThreeReturnUShort_actual :
    griessForm (monsterNortonPairHalfUShortPacket 11)
      monsterNortonOctadThreeInverseSixthPacket = 15 / 16 := by
  rw [monsterNortonPairHalfUShortPacket, form_sum_left]
  simp_rw [short_coefficient, form_symm _ monsterNortonOctadThreeInverseSixthPacket]
  simp only [monsterNortonPairHalfShortUOutput]
  simp_rw [monsterNortonOctadThreeReturnShortGram_actual]
  rw [cast_product_sum, monsterNortonOctadThreeReturnShort_integer]
  norm_num

/-- The complete actual U image has maximal pairing with the actual inverse-sixth packet. -/
theorem monsterNortonOctadThreeReturnU_pairing_one :
    griessForm (y555NortonActualU.val (monsterNortonPairHalfPacket 11))
      monsterNortonOctadThreeInverseSixthPacket = 1 := by
  rw [monsterNortonPairHalfUWhole_actual, map_add, LinearMap.add_apply,
    monsterNortonOctadThreeReturnUMatrix_actual, monsterNortonOctadThreeReturnUShort_actual]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

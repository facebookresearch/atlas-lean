/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual matrix and short pairings for eleven preferred-pair whole returns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfReturnGram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUWholeData
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

private theorem matrix_octad_zero (A : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, A i j = A j i) (d : Fin 759) (v : Fin 64 → ℝ) :
    griessForm (griessConwayDecode (A, (0, 0))) (monsterNortonOctadShortVector d v) = 0 := by
  unfold monsterNortonOctadShortVector
  rw [monsterNortonForm_pure_matrix_raw A 0 _ 0 ha (by intros; rfl)]
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem matrix_symmetric (q : Fin 11) (p : Fin 8) :
    ∀ i j, conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonPairHalfPairIndex (monsterNortonPairReturnCandidate q) p))
        i j = conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonPairHalfPairIndex (monsterNortonPairReturnCandidate q) p))
        j i := conwayMatrixAction_symmetric _ _ (trialityPairMatrix_symmetric _)

private theorem lower_even (q : Fin 11) :
    monsterNortonEvenShortFirstUIsOdd
      ⟨(monsterNortonPairReturnOriginal q).val, by omega⟩ = false := by
  revert q
  decide +kernel

private theorem upper_even (q : Fin 11) :
    monsterNortonEvenShortUpperUIsOdd (monsterNortonPairReturnOriginal q) = false := by
  revert q
  decide +kernel

private theorem lowerPacket (q : Fin 11) :
    monsterNortonShortExtraPacket (monsterNortonEvenShortFirstUOutput
      ⟨(monsterNortonPairReturnOriginal q).val, by omega⟩) =
      monsterNortonOctadShortVector
        (monsterNortonOctadIndex (monsterNortonEvenShortFirstUOctadCodes
          ⟨(monsterNortonPairReturnOriginal q).val, by omega⟩)
          (monsterNortonEvenShortFirstUOctad_weight
            ⟨(monsterNortonPairReturnOriginal q).val, by omega⟩))
        (trialityOctadAction (Pi.single (monsterNortonEvenShortFirstUOctadSign
          ⟨(monsterNortonPairReturnOriginal q).val, by omega⟩) 1)) := by
  simp only [monsterNortonEvenShortFirstUOutput, lower_even q, Bool.false_eq_true,
    ite_false, monsterNortonShortExtraPacket]

private theorem upperPacket (q : Fin 11) :
    monsterNortonShortExtraPacket (monsterNortonEvenShortUpperUOutput
      (monsterNortonPairReturnOriginal q)) = monsterNortonOctadShortVector
        (monsterNortonOctadIndex (monsterNortonEvenShortUpperUOctadCodes
          (monsterNortonPairReturnOriginal q)) (monsterNortonEvenShortUpperUOctad_weight
            (monsterNortonPairReturnOriginal q)))
        (trialityOctadAction (Pi.single (monsterNortonEvenShortUpperUOctadSign
          (monsterNortonPairReturnOriginal q)) 1)) := by
  simp only [monsterNortonEvenShortUpperUOutput, upper_even q, Bool.false_eq_true,
    ite_false, monsterNortonShortExtraPacket]

/-- Each full transported A unit has its exact whole inverse-sixth matrix pairing. -/
theorem monsterNortonPairReturnHalfMatrixGram_actual (q : Fin 11) (p : Fin 8) :
    griessForm (griessConwayDecode (conwayMatrixAction monsterNortonUFiber.val.2
      (trialityPairMatrix (monsterNortonPairHalfPairIndex (monsterNortonPairReturnCandidate q) p)),
      (0, 0))) (monsterNortonEvenShortPairsInverseSixthNormalized
        (monsterNortonPairReturnOriginal q) (monsterNortonPairReturnFamily q)) =
      ((monsterNortonPairReturnBaseSign q *
        (∑ j : Fin 24, monsterNortonPairReturnHalfMatrixNumerator q p j j *
          monsterNortonPairReturnSourceMatrixNumerator q j j) : ℤ) : ℝ) / 512 := by
  unfold monsterNortonEvenShortPairsInverseSixthNormalized
  rw [lowerPacket q, upperPacket q]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [monsterNortonForm_pure_matrix_diagonal _ _ _ (matrix_symmetric q p),
    matrix_octad_zero _ (matrix_symmetric q p), matrix_octad_zero _ (matrix_symmetric q p)]
  simp only [add_zero, mul_zero]
  simp_rw [monsterNortonPairReturnHalfMatrix_actual,
    monsterNortonPairReturnSourceMatrix_actual]
  rw [cast_product_sum, monsterNortonPairReturnBaseSign_actual]
  push_cast
  ring

private theorem short_coefficient (q : Fin 11) (i : NortonPairHalfShortIndex) :
    monsterNortonPairHalfShortCoefficient (monsterNortonPairReturnCandidate q) i =
      (monsterNortonPairReturnShortNumerator q i : ℝ) / 16 := by
  rcases i with ⟨p, s⟩ | ⟨d, e⟩ <;> rfl

/-- The full genuine physical matrix packet contributes one sixteenth in every return case. -/
theorem monsterNortonPairReturnUMatrixPairing_actual (q : Fin 11) :
    griessForm (monsterNortonPairHalfUMatrixPacket (monsterNortonPairReturnCandidate q))
      (monsterNortonEvenShortPairsInverseSixthNormalized (monsterNortonPairReturnOriginal q)
        (monsterNortonPairReturnFamily q)) = 1 / 16 := by
  rw [monsterNortonPairHalfUMatrixPacket, form_sum_left]
  simp_rw [monsterNortonPairReturnHalfMatrixGram_actual]
  rw [cast_product_sum]
  have hi : (∑ p : Fin 8,
      monsterNortonPairHalfPairCoefficient (monsterNortonPairReturnCandidate q) p *
        (monsterNortonPairReturnBaseSign q *
          ∑ j : Fin 24, monsterNortonPairReturnHalfMatrixNumerator q p j j *
            monsterNortonPairReturnSourceMatrixNumerator q j j)) = 512 := by
    calc
      _ = monsterNortonPairReturnBaseSign q *
          (∑ p : Fin 8,
            monsterNortonPairHalfPairCoefficient (monsterNortonPairReturnCandidate q) p *
              ∑ j : Fin 24, monsterNortonPairReturnHalfMatrixNumerator q p j j *
                monsterNortonPairReturnSourceMatrixNumerator q j j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = 512 := monsterNortonPairReturnMatrixPairing_integer q
  rw [hi]
  norm_num

/-- Every complete actual short packet contributes exactly fifteen sixteenths. -/
theorem monsterNortonPairReturnUShortPairing_actual (q : Fin 11) :
    griessForm (monsterNortonPairHalfUShortPacket (monsterNortonPairReturnCandidate q))
      (monsterNortonEvenShortPairsInverseSixthNormalized (monsterNortonPairReturnOriginal q)
        (monsterNortonPairReturnFamily q)) = 15 / 16 := by
  rw [monsterNortonPairHalfUShortPacket, form_sum_left]
  simp_rw [short_coefficient,
    form_symm _ (monsterNortonEvenShortPairsInverseSixthNormalized
      (monsterNortonPairReturnOriginal q) (monsterNortonPairReturnFamily q))]
  simp only [monsterNortonPairHalfShortUOutput]
  simp_rw [monsterNortonPairReturnInverseShortGram_actual]
  rw [cast_product_sum, monsterNortonPairReturnShortPairing_integer]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

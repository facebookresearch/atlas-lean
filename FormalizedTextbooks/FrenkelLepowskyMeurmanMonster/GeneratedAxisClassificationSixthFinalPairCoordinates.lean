/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddlePairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! Final pair coordinates retain the original matrix contribution and preferred short signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual three preferred middle pair rows, cleared by their common denominator four. -/
def generatedSixthMiddlePairNumerator (s : Fin 2) (a b : Fin 24) : ℤ :=
  if s = 0 then
    if a = 16 ∧ b = 17 then 1 else
      if (a = 16 ∧ b = 19) ∨ (a = 17 ∧ b = 19) then -3 else 0
  else 0

/-- The integer table retains the complete preferred signs in the actual middle pair block. -/
theorem generatedSixth_middle_pair_numerator (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inl (s, p)) =
      (generatedSixthMiddlePairNumerator s (griessCoordinatePair p).1
        (griessCoordinatePair p).2 : ℝ) / 4 := by
  rw [generatedSixth_middle_pair_coordinate]
  unfold generatedSixthMiddlePairValue generatedSixthMiddlePairNumerator
  split_ifs <;> norm_num

/-- Off the diagonal, the middle matrix is the genuine transported norm-eight outer over 32. -/
theorem generatedSixth_middle_matrix_pair (p : Fin 276) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).1
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 =
      (generatedSixthNormEightVectorData 8 (griessCoordinatePair p).1 : ℝ) *
        (generatedSixthNormEightVectorData 8 (griessCoordinatePair p).2 : ℝ) / 32 := by
  rw [generatedSixth_middle_matrix]
  have hv (i : Fin 24) : generatedNormEightVector generatedSixthNormEightVector i =
      (generatedSixthNormEightVectorData 8 i : ℝ) / Real.sqrt 8 := by
    simp only [generatedNormEightVector, generatedSixthNormEightVector_val,
      leechCoordinateEmbedding]
    rfl
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    griessCoordinatePair_ne p, ite_false, smul_eq_mul, generatedNormEightLineMatrix,
    Matrix.vecMulVec_apply, mul_zero, zero_add]
  rw [hv, hv]
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
  have hn : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hn]
  rw [hsq]
  ring

/-- Complete final pair numerator; triality mixes both middle short rows and the physical outer. -/
def generatedSixthFinalPairNumerator (s : Fin 2) (p : Fin 276) : ℤ :=
  let a := (griessCoordinatePair p).1
  let b := (griessCoordinatePair p).2
  (if s = 0 then 1 else -1) *
      generatedSixthNormEightVectorData 8 a * generatedSixthNormEightVectorData 8 b +
    4 * (generatedSixthMiddlePairNumerator 0 a b -
      generatedSixthMiddlePairNumerator 1 a b)

/-- Every actual final pair coefficient equals its full signed integer numerator over 32. -/
theorem generatedSixth_final_pair_coordinate (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedSixthAxis).2.1 (Sum.inl (s, p)) =
      (generatedSixthFinalPairNumerator s p : ℝ) / 32 := by
  fin_cases s
  · change (griessConwayEncode generatedSixthAxis).2.1 (Sum.inl (0, p)) =
      (generatedSixthFinalPairNumerator 0 p : ℝ) / 32
    rw [generatedSixthAxis_local_expression, generatedFourthQShortBasis_triality_pair_minus,
      generatedSixth_middle_matrix_pair, generatedSixth_middle_pair_numerator,
      generatedSixth_middle_pair_numerator]
    simp only [generatedSixthFinalPairNumerator, ite_true, Int.cast_add, Int.cast_mul,
      Int.cast_one, Int.cast_sub, Int.cast_ofNat]
    ring
  · change (griessConwayEncode generatedSixthAxis).2.1 (Sum.inl (1, p)) =
      (generatedSixthFinalPairNumerator 1 p : ℝ) / 32
    rw [generatedSixthAxis_local_expression, generatedFourthQShortBasis_triality_pair_plus,
      generatedSixth_middle_matrix_pair, generatedSixth_middle_pair_numerator,
      generatedSixth_middle_pair_numerator]
    simp only [generatedSixthFinalPairNumerator, show (1 : Fin 2) ≠ 0 by decide,
      ite_false, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_one,
      Int.cast_sub, Int.cast_ofNat]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

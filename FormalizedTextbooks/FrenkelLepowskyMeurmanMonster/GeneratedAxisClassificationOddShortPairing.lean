/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddMonomialSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddQStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProduct

/-! The genuine odd-axis short coefficients are determined by its matrix
pairing and the original pair-spin eigenvalues. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original odd-axis pair coordinate is its actual eigenvalue times a
matrix-pairing coefficient. This binds all 552 original short coordinates. -/
theorem generatedOddAxis_short_pairing (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedOddAxis).2.1 (Sum.inl (s, p)) =
      qSign (generatedOddPairEigenSign s) *
        (1 / 2 - conwayShortPairing (griessConwayEncode generatedOddAxis).1
          (Sum.inl (s, p)) / 4) := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  rw [generatedOddAxis, generatedAxis_triality_odd_pair_coordinate,
    generatedAxis_triality_odd_matrix, conwayShortPairing_diagonal_pair]
  have hn := griessCoordinatePair_ne p
  have hsign : qSign (generatedOddPairEigenSign s) = (if s = 0 then 1 else -1) := by
    fin_cases s <;> norm_num [generatedOddPairEigenSign]
  rw [hsign]
  congr 1
  simp only [griessShortVector, griessShortIntegral, Fin.val_zero, hm,
    Nat.zero_testBit, Bool.false_eq_true, ite_false]
  by_cases ha : (griessCoordinatePair p).1 = 0
  · have hb : (griessCoordinatePair p).2 ≠ 0 := by
      intro hb
      exact hn (ha.trans hb.symm)
    simp only [ha, hb, ite_true, ite_false]
    norm_num only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_one]
    field_simp
    nlinarith only [hs]
  · by_cases hb : (griessCoordinatePair p).2 = 0
    · simp only [ha, hb, ite_true, ite_false]
      norm_num only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      field_simp
      nlinarith only [hs]
    · simp only [ha, hb, ite_false]
      norm_num only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      field_simp
      nlinarith only [hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

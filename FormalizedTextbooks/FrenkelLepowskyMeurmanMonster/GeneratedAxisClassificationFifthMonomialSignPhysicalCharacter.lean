/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPhaseFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignFourierCharacter
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorFourier

/-! Actual physical sign characters from an eight-coordinate normalized intersection certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem sign_injective : Function.Injective qSign := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | norm_num [qSign] at h

/-- The cached physical character is the actual original octad negative-position character. -/
theorem generatedFifth_sign_negative_character_qSign (f : Fin 2048) (j : Fin 56)
    (e : Fin 64) :
    qSign (generatedFifthSignNegativeCharacter ⟨f.val, by omega⟩ j e) =
      octadNegativeCharacter (generatedFifthEvenRootOctad j) e f := by
  unfold octadNegativeCharacter
  apply congrArg qSign
  rw [golaySyndrome_spinDot]
  unfold generatedFifthSignNegativeCharacter
  apply Finset.sum_congr rfl
  intro i _
  rw [show octadSpinLow f = golayLabelCoefficients ⟨f.val, by omega⟩ by rfl,
    golayLabelEncoder_boolean]
  change _ = integerParity (fun i =>
    if (griessOctadSignMask (generatedFifthEvenRootOctad j) e).testBit i.val
      then (1 : ℤ) else 0) i * _
  rw [← generatedFifthXiShortCachedSignMask_actual]
  cases h : (generatedFifthXiShortCachedSignMask j e).testBit i.val <;>
    simp [integerParity, h, golayBooleanCast]

/-- Eight actual coordinate bits identify the genuine original Walsh character label. -/
theorem generatedFifth_sign_character_label_of_bits (f : Fin 2048) (j : Fin 56) (l : Fin 64)
    (hb : ∀ k : Fin 8, trialityBinaryBit l k =
      golayBooleanCast ((golayEncodedMask f.val).testBit
        (generatedFifthEvenRootCoordinates j k).val) +
        golayBooleanCast ((golayEncodedMask f.val).testBit
          (generatedFifthEvenRootCoordinates j 7).val)) :
    octadTensorCharacterLabel (generatedFifthEvenRootOctad j) f = l := by
  apply octadSignLabelEquiv.injective
  apply octadSignRepresentative_injective
  ext k
  rw [octadSignRepresentative_label, octadSignRepresentative_label,
    octadTensorCharacterLabel_bits]
  simp only [octadTensorRestriction, octadSpinLow, golayLabelEncoder_boolean]
  rw [generatedFifth_even_coordinates_certificate j k,
    generatedFifth_even_coordinates_certificate j 7]
  exact (hb k).symm

/-- A verified eight-bit intersection and cached source row determine every actual binary phase. -/
theorem generatedFifth_sign_negative_character_of_row (f : Fin 2048) (j : Fin 56)
    (l : Fin 64) (S : Fin 64 → ZMod 2)
    (hb : ∀ k : Fin 8, trialityBinaryBit l k =
      golayBooleanCast ((golayEncodedMask f.val).testBit
        (generatedFifthEvenRootCoordinates j k).val) +
        golayBooleanCast ((golayEncodedMask f.val).testBit
          (generatedFifthEvenRootCoordinates j 7).val))
    (hs : ∀ e : Fin 64, (if S e = 0 then (1 : ℤ) else -1) =
      (if S 0 = 0 then (1 : ℤ) else -1) * generatedFifthSignHadamardCache l e)
    (e : Fin 64) :
    generatedFifthSignNegativeCharacter ⟨f.val, by omega⟩ j e = S e + S 0 := by
  have hn : qSign (generatedFifthSignNegativeCharacter ⟨f.val, by omega⟩ j e) =
      (generatedFifthSignHadamardCache l e : ℝ) := by
    rw [generatedFifth_sign_negative_character_qSign, octadTensorCharacterLabel_character,
      generatedFifth_sign_character_label_of_bits f j l hb, generatedFifth_sign_hadamard_cache]
  have hc : qSign (S e) = qSign (S 0) * (generatedFifthSignHadamardCache l e : ℝ) := by
    simpa only [Int.cast_ite, Int.cast_one, Int.cast_neg, Int.cast_mul, qSign] using
      congrArg (fun x : ℤ => (x : ℝ)) (hs e)
  apply sign_injective
  rw [hn, qSign_add, hc]
  rw [mul_comm (qSign (S 0)) _, mul_assoc, qSign_sq, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
